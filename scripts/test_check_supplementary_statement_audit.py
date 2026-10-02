"""Missing or stale manual assessments must not silently pass coverage gates."""
import json

import check_supplementary_statement_audit as supplementary


def snapshot():
    return json.loads(supplementary.AUDIT.read_text())


def test_current_supplement_covers_remaining_statements():
    assert len(supplementary.expected_items()) == 40
    assert supplementary.validate(snapshot()) == []


def test_missing_or_duplicate_assessment_is_rejected():
    data = snapshot()
    removed = data["items"].pop()
    data["items"].append(data["items"][0])
    errors = supplementary.validate(data)
    assert f"missing supplementary label {removed['latex_label']}" in errors
    assert any("duplicate supplementary label" in error for error in errors)


def test_stale_source_and_lean_context_are_rejected():
    data = snapshot()
    data["lean_context_hash"] = "changed"
    data["items"][0]["statement_hash"] = "changed"
    errors = supplementary.validate(data)
    assert "supplementary audit lean_context_hash is stale" in errors
    assert any("statement_hash is stale" in error for error in errors)


def test_empty_selection_is_rejected(monkeypatch):
    monkeypatch.setattr(supplementary, "expected_items", lambda: {})
    assert supplementary.validate(snapshot()) == [
        "no supplementary statements selected; refusing an empty audit"]
