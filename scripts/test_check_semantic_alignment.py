"""Regressions for the previously empty semantic-alignment audit."""
import check_semantic_alignment as alignment


def test_real_corpus_cannot_silently_skip_theorem_audit():
    items = alignment.theorem_items()
    assert len(items) == 30
    assert {item['latex_label'] for item in items} >= {
        'thm:closure:strong-bsd-conditional',
        'thm:closure:composite-signature',
        'thm:apparatus:vsrc-stage-iii-translation',
    }
    assert all(item['statement_hash'] and item['lean_decl'] for item in items)


def test_missing_alignment_is_rejected():
    errors = alignment.validate({})
    assert len(errors) == len(alignment.theorem_items())
    assert any('strong-bsd-conditional' in error for error in errors)


def test_manuscript_read_is_live(monkeypatch):
    current, _, _ = alignment.collect_records()
    label = 'thm:closure:strong-bsd-conditional'
    current = [dict(item) for item in current]
    next(item for item in current if item['latex_label'] == label)['statement_hash'] = 'changed'
    monkeypatch.setattr(alignment, 'collect_records', lambda: (current, [], []))
    item = next(item for item in alignment.theorem_items() if item['latex_label'] == label)
    assert item['statement_hash'] == 'changed'


def test_lean_context_change_invalidates_reviewed_alignments(monkeypatch):
    entries = {item['latex_label']: alignment.default_entry(item)
               for item in alignment.theorem_items()}
    monkeypatch.setattr(alignment, 'lean_context_hash', lambda: 'changed')
    errors = alignment.validate(entries)
    assert len(errors) == 30
    assert all('lean_context_hash is stale' in error for error in errors)


def test_empty_selection_cannot_pass(monkeypatch):
    monkeypatch.setattr(alignment, 'theorem_items', lambda: [])
    errors, _ = alignment.check_or_generate(check=True)
    assert errors == ['no theorem-like Lean declarations selected; refusing an empty semantic audit']
