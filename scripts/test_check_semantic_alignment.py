"""Regressions for the previously empty semantic-alignment audit."""
import check_semantic_alignment as alignment


def test_real_corpus_cannot_silently_skip_theorem_audit():
    items = alignment.theorem_items()
    assert len(items) == 29
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
