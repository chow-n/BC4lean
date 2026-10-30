#!/usr/bin/env python3
"""Verify genuine Chapter 8 assembly milestones while keeping the general conjecture pending.

Native acceptance requires four actual subprocesses and unchanged inputs.
Generation-only mode runs no native process and makes no proof claim."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import signal
import time
import subprocess
import sys
import tempfile
import types
import uuid

SCHEMA = "chapter8.actual.native-milestone-audit.v1"
DIRECTORY = "docs/audits/chapter8"
INVENTORY = DIRECTORY + "/inventory.json"
FIXTURE = DIRECTORY + "/ExpectedTypes.lean"
BASELINE = DIRECTORY + "/Chapter7Baseline.json"
IMPORTS = DIRECTORY + "/Chapter7Imports.lean"
BLUEPRINT = "blueprint/src/parts/08-conjecture-and-examples.tex"
RETAINED = "scripts/check_chapter7_retained.py"
RETAINED_PROVIDER_SHA = "dcc7a783f842e8196b71bd6e1499e00821e98214e8efbc81bc648ca41628d7d8"
# Candidate independently reviewed formulas. A native syntax repair must retain
# the actual assembly signatures and receive a new explicit reviewed binding.
EXPECTED_TYPES_SHA = "3eb143fa0b3051dfde0ed01836b12c7178a81f1b4ef666ea33a0d5fee004d23e"
SOURCE7 = "4daf13f6be649ef3e7f9fe90122bcbee4707b1b2"
PUBLICATION7 = "e1afa3d693e0a95cd568f517578d109995d80442"
PREFIX7_SHA = "309158d81f7d7994edab43ce59a9e7820f1fa5c5f364321cd3bf6f327c7f00bc"
BASELINE_SHA = "1518087f749f7a6cf0b61b1cfae442ab34f22e4864371f96a1f8dee0454c3035"
COMPILER_LOCK = Path("/tmp/bc4lean-ch7-lean.lock")
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
PROPERTY = "BC4lean.Assembly.BaumConnesProperty"
CONJECTURE = "BC4lean.Assembly.BaumConnesConjecture"
UNIT = "BC4lean.Chapter8Examples.baumConnesProperty_unit"
REQUIRED_KINDS = {PROPERTY: "definition", CONJECTURE: "definition", UNIT: "theorem"}
SUPPORT_DATA_KINDS = {"BC4lean.KKTheory.UnitScalarDescent." + n: "definition" for n in
                      ("evenCoefficientRestrictionIso", "oddCoefficientRestrictionIso")}
MODULES = sorted("BC4lean." + name for name in (
    "BaumConnesProperty", "BaumConnesInvariance", "AssemblyBijectivityCriteria",
    "TrivialAnalyticCalibration", "CompactModelColimitCalibration", "FiniteGroupPointCalibration",
    "UnitScalarDescent", "ScalarUnitProjection", "UnitPointCutoff", "UnitAssemblyEquivalence",
    "FinitePointCutoff", "FiniteReducedGroupCStar", "KKGroupRestriction", "SubsingletonScalarDescent",
    "ScalarIdentityUniverse", "SubsingletonAssemblyEquivalence", "ScalarProjectionRank",
    "ScalarOperatorK0", "ScalarOperatorK1", "ScalarOperatorKNonunital", "TrivialAnalyticScalar",
    "FinitePointCharacterTensor", "FinitePointCompressedDescent", "KasparovReducingCompression",
    "KasparovReducingCompressionFibre", "OrderTwoPointKK", "OrderTwoEigenSplitInvariance",
    "KasparovGroupChange", "OrderTwoEigenSplitAdditive", "OrderTwoPointKKSplit", "OrderTwoPointKKScalar",
    "OrderTwoAssemblyEquivalence"))
NAME = re.compile(r"BC4lean(?:\.[A-Za-z_][A-Za-z0-9_']*)+\Z")
HASH = re.compile(r"[0-9a-f]{64}\Z")
REV = re.compile(r"[0-9a-f]{40}\Z")
CONTROLS = [BLUEPRINT, INVENTORY, FIXTURE, BASELINE, IMPORTS, "BC4lean.lean", RETAINED,
    "scripts/test_chapter7_retained.py", "scripts/audit_chapter8.py", "scripts/test_audit_chapter8.py",
    "scripts/chapter8_publication_core.py", "scripts/chapter8_publication_runtime.py",
    "scripts/update_chapter8_finder.py", "scripts/test_chapter8_publication.py",
    "scripts/check_chapter8_website.py", "scripts/verify_live_chapter8.py",
    "scripts/run_chapter8_publication_tests.py", DIRECTORY + "/RendererScaffold.json",
    ".github/workflows/chapter7.yml", ".github/workflows/chapter8.yml",
    ".github/workflows/blueprint.yml", ".github/workflows/blueprint-check.yml",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/check_project_imports.py"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(relative):
    require(isinstance(relative, str) and relative and "\\" not in relative
            and not any(c in relative for c in "\0\r\n"), "Unsafe audit path")
    path = PurePosixPath(relative)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == relative,
            "Audit path escapes/cannot be canonicalized")
    return relative


def bounded_file(path):
    require(not path.is_symlink() and path.is_file() and path.stat().st_size <= 8 * 1024 * 1024,
            "Unsafe/oversized retained audit evidence")
    with path.open("rb") as stream:
        data = stream.read(8 * 1024 * 1024 + 1)
    require(len(data) <= 8 * 1024 * 1024, "Audit input grew past read budget")
    return data


def read(root, relative):
    path = root / safe(relative)
    require(path.resolve(strict=True).is_relative_to(root.resolve()), "Audit input escapes current root")
    return bounded_file(path)


def obj(data, label):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"Duplicate JSON key: {label}/{key}")
            result[key] = value
        return result
    value = json.loads(data, object_pairs_hook=unique)
    require(isinstance(value, dict), f"Expected object: {label}")
    return value


def names(values, label, empty=False):
    require(isinstance(values, list) and (values or empty)
            and all(isinstance(n, str) and NAME.fullmatch(n) for n in values)
            and len(values) == len(set(values)), f"Invalid/duplicate exact names: {label}")
    return sorted(values)


def load_inventory(path, captured=None):
    value = obj(bounded_file(path) if captured is None else captured, "inventory")
    require(value.get("schema_version") == 1, "Unsupported Chapter8 inventory schema")
    value["modules"] = names(value.get("modules"), "modules")
    require(value["modules"] == MODULES and value.get("additional_source_modules") == [],
            "Chapter8 scope must contain exactly the intended new modules")
    require(set(value.get("targets", {})) == {"def:baum-connes-property", "conj:baum-connes"},
            "The two original Chapter8 targets must remain explicit")
    require(value["targets"]["def:baum-connes-property"].get("statement_kind") == "definition",
            "Original Baum-Connes property must remain a definition")
    require(value["targets"]["conj:baum-connes"].get("status") == "pending"
            and value["targets"]["conj:baum-connes"].get("required_declarations") == []
            and value["targets"]["conj:baum-connes"].get("statement_kind") == "conjecture"
            and bool(value["targets"]["conj:baum-connes"].get("blocked_reason")),
            "General conjecture must remain pending without an assumed proof endpoint")
    require(value.get("statement_definition_declarations") == {"conj:baum-connes": [CONJECTURE]},
            "The general statement is a named Prop definition, never a theorem/axiom")
    require(value.get("required_declaration_kinds") == REQUIRED_KINDS,
            "Property/general must be definitions and closed Unit endpoint must be a theorem")
    require(isinstance(value.get("milestones"), dict) and "thm:baum-connes-unit" in value["milestones"],
            "Genuine Unit assembly theorem milestone is required")
    require(value["milestones"]["thm:baum-connes-unit"].get("statement_kind") == "theorem",
            "Unit milestone must be the actual theorem, not a conditional assumption label")
    for label, item in {**value["targets"], **value["milestones"]}.items():
        require(isinstance(label, str) and re.fullmatch(r"[A-Za-z][A-Za-z0-9:_-]*", label), "Bad statement label")
        if label == "conj:baum-connes": continue
        require(item.get("status") in {"candidate", "implemented"}
                and item.get("statement_kind") in {"definition", "proposition", "theorem", "lemma"},
                "Candidate/implemented status and exact statement kind required")
        item["required_declarations"] = names(item.get("required_declarations"), label)
    require(PROPERTY in value["targets"]["def:baum-connes-property"]["required_declarations"]
            and UNIT in value["milestones"]["thm:baum-connes-unit"]["required_declarations"],
            "Original property and unassumed Unit theorem endpoints may not be dropped")
    value["intended_endpoints"] = names(value.get("intended_endpoints"), "intended mathematical endpoints")
    value["expected_type_endpoints"] = names(value.get("expected_type_endpoints"), "independent typed endpoints")
    value["blueprint_required_endpoints"] = names(value.get("blueprint_required_endpoints"), "blueprint links")
    union = {CONJECTURE} | {n for item in [*value["targets"].values(), *value["milestones"].values()]
                                for n in item["required_declarations"]}
    require(value["intended_endpoints"] == value["expected_type_endpoints"]
            and set(value["blueprint_required_endpoints"]) == union
            and {PROPERTY, CONJECTURE, UNIT} <= set(value["expected_type_endpoints"]),
            "Independent typed endpoint and blueprint-link inventories differ from intended statements")
    require(value.get("blueprint_support_data_kinds") == SUPPORT_DATA_KINDS
            and union - set(value["expected_type_endpoints"]) == set(SUPPORT_DATA_KINDS)
            and set(SUPPORT_DATA_KINDS).isdisjoint(value["expected_type_endpoints"]),
            "Only the two explicit coefficient-restriction cycle data definitions lack separate fixture examples")
    require(type(value.get("expected_type_examples")) is int and value["expected_type_examples"] >= 60,
            "Independent endpoint fixture must retain its substantive checks")
    return value


def check_statement_definition_metadata(audit, inventory):
    require(audit.get("statement_definition_declarations") == inventory["statement_definition_declarations"],
            "General conjecture source link must retain the exact separate Prop-definition metadata")


def audit_blueprint(text, inventory, trusted):
    text = trusted.tex_code_only(text)
    def links(body):
        groups = re.findall(r"\\lean\{([^}]*)\}", body)
        require(all(n.strip() for group in groups for n in group.split(",")), "Empty Lean link")
        return names(sorted({n.strip() for group in groups for n in group.split(",")}), "blueprint links", True)
    expected = {**inventory["targets"], **inventory["milestones"]}
    found, targets = {}, {}
    blocks = list(re.finditer(r"\\begin\{(definition|proposition|theorem|lemma|conjecture)\}(.*?)\\end\{\1\}", text, re.S))
    for match in blocks:
        labels = re.findall(r"\\label\{([^}]+)\}", match[2])
        require(len(labels) == 1 and labels[0] in expected and labels[0] not in found,
                "Unregistered/duplicate/unlabelled Chapter8 statement")
        label = labels[0]; item = expected[label]; body = match[2]
        require(match[1] == item["statement_kind"], "Original/registered statement kind changed")
        pending = len(re.findall(r"\\notready\b", body)); ready = len(re.findall(r"\\leanok\b", body))
        actual = links(body)
        require(pending <= 1 and ready <= 1 and not (pending and ready), "Contradictory/repeated readiness markers")
        required = item["required_declarations"]
        if label == "conj:baum-connes":
            require(pending == 1 and ready == 0 and CONJECTURE in actual,
                    "General conjecture remains pending despite its Prop-definition source link")
        elif item["status"] == "implemented":
            require(pending == 0 and ready == 1 and set(required) <= set(actual),
                    "Implemented statement lacks actual endpoint links and checked status")
        else:
            require(pending == 1 and ready == 0, "Unaccepted candidate cannot carry a checked marker")
        proof = re.match(r"\\begin\{proof\}(.*?)\\end\{proof\}", text[match.end():].lstrip(), re.S)
        is_ready = label != "conj:baum-connes" and item["status"] == "implemented"
        if label == "conj:baum-connes":
            require(not proof or not re.search(r"\\leanok\b", proof[1]), "General conjecture has a false checked proof")
        elif is_ready and match[1] != "definition":
            require(proof is not None and re.search(r"\\leanok\b", proof[1])
                    and not re.search(r"\\notready\b", proof[1]), "Genuine theorem/proposition lacks checked attached proof")
        found[label] = True
        targets[label] = {"statement_kind": match[1], "ready": is_ready, "notready": bool(pending),
                          "leanok": bool(ready), "required_declarations": required,
                          "linked_declarations": actual, "explicit_checked_proof": bool(proof and is_ready)}
    require(set(found) == set(expected), "A registered original target/milestone is missing")
    all_links = links(text)
    require(inventory["blueprint_required_endpoints"] == all_links, "Exact intended blueprint endpoint links differ")
    return all_links, {k: targets[k] for k in inventory["targets"]}, {k: targets[k] for k in inventory["milestones"]}


def check_sources(source, label, trusted):
    trusted.check_proof_tokens(source, label)
    trusted.check_strict_options(source, label)
    trusted.check_no_environment_patches(source, label)
    trusted.check_legacy_module(source, label)
    allowed = {"autoImplicit": "false", "relaxedAutoImplicit": "false", "warningAsError": "true"}
    for option, value in re.findall(r"\bset_option\s+(\S+)\s+(\S+)", trusted.code_only(source)):
        require(allowed.get(option) == value, f"Ordinary source proof budgets/options must not be raised: {label}/{option}")


def validate_fixture(data, inventory, trusted):
    require(sha(data) == EXPECTED_TYPES_SHA, "Independent actual assembly/closed-Unit formula fixture lacks its reviewed binding")
    text = data.decode(); check_sources(text, "independent fixture", trusted)
    require(len(re.findall(r"(?m)^example\b", trusted.code_only(text))) == inventory["expected_type_examples"],
            "Independent fixture lost substantive explicit signatures")
    endpoints = set(re.findall(r"(?m)^-- endpoint: (BC4lean(?:\.[A-Za-z_][A-Za-z0-9_']*)+)(?:\s|$)", text))
    require(endpoints == set(inventory["expected_type_endpoints"]),
            "Inventory must retain all independently typed mathematical endpoints")


def generate_query(modules, links, endpoints, trusted):
    query = trusted.generate_query(modules, links, endpoints).replace("CH7_", "CH8_").replace("Chapter 7", "Chapter 8")
    needle = '    Lean.Elab.Command.liftIO <| IO.println s!"CH8_DECL|{origin}|{name.toString}|{axiomText}"'
    extra = '''
    let some info := env.find? name
      | throwError "Missing declaration metadata {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_KIND|{name.toString}|{kind}"'''
    require(query.count(needle) == 1, "Frozen metadata query changed; review Chapter8 adaptation")
    return query.replace(needle, needle + extra)


def parse_kernel(output, modules, links, endpoints, required_kinds, trusted):
    kinds, ordinary, inside = {}, [], False
    for line in output.splitlines():
        if line == "CH8_START|1": inside = True
        if line.startswith("CH8_KIND|"):
            fields = line.split("|")
            require(inside and len(fields) == 3 and fields[1] and fields[1] not in kinds
                    and fields[2] in {"definition", "theorem", "opaque", "quotient", "inductive", "constructor", "recursor"},
                    "Malformed/duplicate/axiomatic new declaration kind")
            kinds[fields[1]] = fields[2]
        else:
            ordinary.append(line.replace("CH8_", "CH7_") if line.startswith("CH8_") else line)
        if line.startswith("CH8_END|"): inside = False
    data = trusted.parse_kernel_evidence("\n".join(ordinary), modules, links, endpoints)
    require(set(kinds) == {row["name"] for row in data["declarations"]},
            "Kind census must cover every private/generated/new declaration without a cap")
    require(all(kinds.get(name) == kind for name, kind in required_kinds.items()),
            "Property/general are definitions; genuine unassumed Unit endpoint must be a theorem")
    data["declaration_kinds"] = kinds
    return data


@contextmanager
def retained_module(root, captured_code=None):
    path = root / RETAINED
    code = read(root, RETAINED) if captured_code is None else captured_code
    require(sha(code) == RETAINED_PROVIDER_SHA, "Retained provider is not the exact reviewed production adapter")
    name = "_chapter8_retained_" + uuid.uuid4().hex
    module = types.ModuleType(name); module.__file__ = str(path)
    require(name not in sys.modules, "Temporary provider module collision")
    sys.modules[name] = module
    try:
        exec(compile(code, str(path), "exec"), module.__dict__)
        yield module
    finally:
        sys.modules.pop(name, None)


def sidecar(output, suffix):
    return output.with_suffix("." + suffix)


def validate_output_scope(root, requested):
    """Protect all repository proof/control/history paths before the first write."""
    require(not requested.is_symlink(), "Audit output cannot be a symlink")
    output = requested.resolve()
    require(output.suffix == ".json", "Audit output must use its reserved .json/sidecar namespace")
    if output.is_relative_to(root):
        require(output == root / DIRECTORY / "audit.json",
                "Repository audit output is restricted to docs/audits/chapter8/audit.json")
    suffixes = ["lean", "inputs.json", "retained-preservation.json"]
    for stage in ["retained-preservation", "build-gate", "expected-types", "kernel"]:
        suffixes += [stage + ".log", stage + "-run.json"]
    for path in [output] + [sidecar(output, suffix) for suffix in suffixes]:
        require(not path.is_symlink() and path.resolve().parent == output.parent,
                "Reserved audit sidecar is a symlink or escapes its output directory")
    return output


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path, value):
    """Atomically retain each real phase record before starting the next phase."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp-" + uuid.uuid4().hex)
    try:
        with temporary.open("x") as handle:
            handle.write(json.dumps(value, indent=2) + "\n")
            handle.flush(); os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


class CompilerLease:
    def __init__(self, directory, owner):
        self.directory, self.owner = directory, owner
        self.release_safe = True

    def phase(self, stage, child_pid=None, process_group=None):
        current = obj((self.directory / "owner.json").read_bytes(), "compiler owner")
        require(current == self.owner, "Compiler ownership changed; no further native action authorized")
        self.owner = {**self.owner, "phase": stage, "updated_utc": utc_now(), "child_pid": child_pid, "process_group": process_group}
        write_json(self.directory / "owner.json", self.owner)


@contextmanager
def compiler_lock(root, output, run_id, directory=COMPILER_LOCK):
    """Never retire an existing/unknown mutex, even if its PID looks stale."""
    try:
        directory.mkdir()
    except FileExistsError as error:
        raise ValueError("Compiler mutex occupied; no actual audit subprocess started") from error
    owner = {"schema": "chapter8.compiler-owner.v1", "pid": os.getpid(), "run_id": run_id,
             "phase": "audit-prerequisites", "source_root": str(root), "output": str(output),
             "started_utc": utc_now(), "updated_utc": utc_now(), "child_pid": None}
    lease = CompilerLease(directory, owner)
    try:
        write_json(directory / "owner.json", owner)
        yield lease
    finally:
        # A changed owner is not ours to erase. Preserve the mutex and evidence.
        path = directory / "owner.json"
        if lease.release_safe and path.is_file() and obj(path.read_bytes(), "compiler owner") == lease.owner:
            path.unlink()
            try: directory.rmdir()
            except OSError: pass


def owned_group_exists(group):
    require(type(group) is int and group > 0 and group != os.getpgrp(), "Invalid owned child process group")
    try:
        os.killpg(group, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True  # Cannot establish quiescence; retain ownership.


def wait_group_quiet(group, seconds):
    deadline = time.monotonic() + seconds
    while owned_group_exists(group):
        if time.monotonic() >= deadline: return False
        time.sleep(0.02)
    return True


def stop_owned_process_group(process):
    """Signal only the new session/group created for this exact child PID."""
    group = process.pid
    require(group != os.getpgrp(), "Refusing to signal the auditor's process group")
    for signum in (signal.SIGTERM, signal.SIGKILL):
        try: os.killpg(group, signum)
        except ProcessLookupError: pass
        except PermissionError: return False
        try: process.wait(timeout=1)
        except subprocess.TimeoutExpired: pass
        if wait_group_quiet(group, 1): return True
    return False


def run_process(root, command, output, stage, lease, run_id, **metadata):
    lease.phase(stage)
    log = sidecar(output, stage + ".log")
    record_path = sidecar(output, stage + "-run.json")
    record = {"schema": "chapter8.actual.process.v1", "status": "starting", "stage": stage,
              "run_id": run_id, "parent_pid": os.getpid(), "source_root": str(root),
              "command": command, "started_utc": utc_now(), **metadata}
    write_json(record_path, record)
    process = None
    spawn_attempted = False
    try:
        # A private session/group lets interruption stop all owned descendants.
        # Stream to a durable raw file: a disconnect cannot discard PIPE data.
        with log.open("wb") as handle:
            spawn_attempted = True
            lease.release_safe = False
            process = subprocess.Popen(command, cwd=root, stdout=handle, stderr=subprocess.STDOUT,
                                       start_new_session=True,
                                       env={**os.environ, "LEAN_NUM_THREADS": "1"})
            record.update(status="running", pid=process.pid, process_group=process.pid)
            write_json(record_path, record); lease.phase(stage, process.pid, process.pid)
            exit_code = process.wait()
            require(wait_group_quiet(process.pid, 0.2), "Actual child exited with active owned descendants")
            lease.release_safe = True
            handle.flush(); os.fsync(handle.fileno())
        record.update(status="completed", exit_code=exit_code, finished_utc=utc_now(),
                      owned_process_group_quiescent=True, stdout_stderr_sha256=sha(bounded_file(log)))
        write_json(record_path, record); lease.phase(stage + "-finished")
    except BaseException as error:
        quiet = not spawn_attempted
        if process is not None:
            try: quiet = stop_owned_process_group(process)
            except (OSError, ValueError, subprocess.TimeoutExpired): quiet = False
        lease.release_safe = quiet
        record.update(status="interrupted", finished_utc=utc_now(), error=type(error).__name__,
                      owned_process_group_quiescent=quiet)
        if log.is_file(): record["stdout_stderr_sha256"] = sha(bounded_file(log))
        write_json(record_path, record)
        if not quiet:
            pid = process.pid if process is not None else None
            lease.phase(stage + "-cleanup-unconfirmed-retain-mutex", pid, pid)
        raise
    require(type(record["exit_code"]) is int and record["exit_code"] == 0, f"Actual {stage} subprocess failed")
    return record, bounded_file(log)


def validate_process_record(record, stage, run_id, origin):
    require(record.get("schema") == "chapter8.actual.process.v1" and record.get("status") == "completed"
            and record.get("stage") == stage and record.get("run_id") == run_id
            and isinstance(run_id, str) and re.fullmatch(r"[0-9a-f]{32}", run_id)
            and record.get("source_root") == origin
            and type(record.get("pid")) is int and record["pid"] > 0
            and type(record.get("parent_pid")) is int and record["parent_pid"] > 0
            and type(record.get("process_group")) is int and record["process_group"] == record["pid"]
            and record.get("owned_process_group_quiescent") is True
            and type(record.get("exit_code")) is int and record["exit_code"] == 0,
            "Raw process lacks completed actual invocation/ownership provenance")
    try:
        start = datetime.fromisoformat(record["started_utc"])
        finish = datetime.fromisoformat(record["finished_utc"])
    except (KeyError, TypeError, ValueError) as error:
        raise ValueError("Raw actual process timestamps missing/malformed") from error
    require(start.utcoffset() is not None and finish.utcoffset() is not None and finish >= start,
            "Raw actual process completion precedes its start")
    return start, finish


def current_import_check(root, code):
    namespace = {"__name__": "_chapter8_import_coverage", "__file__": str(root / "scripts/check_project_imports.py")}
    exec(compile(code, namespace["__file__"], "exec"), namespace)
    errors = namespace["check"](root) + namespace["check_chapter5_core_evidence"](root)
    require(not errors, "Current complete importer/historical core check failed: " + "; ".join(errors))
    return {"status": "validated_current_import_coverage", "errors": [], "script_sha256": sha(code)}


def check_retained_receipt(value, modules):
    require(value.get("schema") == "chapter7.retained.preservation.prototype.v1"
            and value.get("status") == "verified_q7_preservation_and_registered_import_extension_only"
            and value.get("source_revision_s7") == SOURCE7 and value.get("publication_revision_q7") == PUBLICATION7
            and value.get("proof_sources_preserved") == 930 and value.get("original_input_bindings") == 145
            and value.get("canonical_artifacts_preserved") == 21
            and value.get("historical_declarations") == 2491 and value.get("historical_exact_links") == 117
            and value.get("historical_independent_signatures") == 55 and value.get("historical_strict_build_runs") == 106
            and set(value.get("historical_axioms", [])) == ALLOWED
            and value.get("registered_future_modules") == modules
            and value.get("chapter8_complete") is False
            and value.get("chapter8_native_verification_performed") is False,
            "Retained Chapter7 preservation receipt lacks the exact real baseline/extension scope")


def capture(root, inventory, provider):
    baseline = read(root, BASELINE)
    require(sha(baseline) == BASELINE_SHA, "Original Q7 baseline manifest changed")
    manifest = provider.load_manifest(baseline)
    paths = set(CONTROLS) | set(manifest["proof_sources"]) | set(manifest["original_inputs"]) \
        | set(manifest["canonical_artifacts"]) | set(manifest["trusted_pure_helpers"])
    paths |= {m.replace(".", "/") + ".lean" for m in inventory["modules"]}
    require(len(paths) <= 4096, "Unbounded input inventory")
    data = {path: read(root, path) for path in sorted(paths)}
    require(sum(map(len, data.values())) <= 128 * 1024 * 1024, "Source snapshot exceeds total budget")
    return manifest, data


def build_replay(root, build, raw, inventory, hashes, trusted):
    require(build.get("status") == "passed" and build.get("sources_unchanged_during_build") is True
            and build.get("sequential_leaf_builds") is True and build.get("environment") == {"LEAN_NUM_THREADS": "1"}
            and build.get("combined_log_sha256") == sha(raw), "Actual full Chapter8 strict build is incomplete or changed")
    modules = inventory["modules"]; runs = build.get("runs")
    require(isinstance(runs, list) and len(runs) == len(modules) + 1, "Full build needs every new leaf plus aggregate")
    markers = list(re.finditer(rb"(?m)^COMMAND ([^\n]+)\n", raw))
    require(len(markers) == len(runs) and markers[0].start() == 0, "Actual Chapter8 combined log framing differs")
    targets = []
    previous_finish = None
    for index, (run, marker) in enumerate(zip(runs, markers)):
        command = run.get("command")
        require(isinstance(command, list) and len(command) == 5
                and command[:4] == ["lake", "--wfail", "--no-cache", "build"]
                and type(run.get("exit_code")) is int and run["exit_code"] == 0
                and marker[1] == json.dumps(command).encode(), "Actual strict build run/command differs")
        segment = raw[marker.end():markers[index + 1].start() if index + 1 < len(markers) else len(raw)]
        require(sha(segment) == run.get("stdout_stderr_sha256"), "Actual strict build raw segment differs")
        try:
            start, finish = datetime.fromisoformat(run["started_utc"]), datetime.fromisoformat(run["finished_utc"])
        except (KeyError, TypeError, ValueError) as error:
            raise ValueError("Full strict build run lacks actual start/finish timestamps") from error
        require(start.utcoffset() is not None and finish.utcoffset() is not None and finish >= start
                and (previous_finish is None or start >= previous_finish), "Actual full-build runs overlap/reorder")
        previous_finish = finish
        targets.append(command[-1])
    require(targets[-1] == "BC4lean" and len(set(targets[:-1])) == len(modules)
            and set(targets[:-1]) == set(modules), "New-leaf/aggregate build coverage differs")
    input_map = build.get("all_input_sha256")
    require(isinstance(input_map, dict), "Actual full build lacks its all-input source bindings")
    old = obj(read(root, BASELINE), "baseline")["proof_sources"]
    required = set(old) | {m.replace(".", "/") + ".lean" for m in modules} | {
        INVENTORY, IMPORTS, "BC4lean.lean", "scripts/audit_chapter6.py",
        "lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    order = build.get("order_validation", {})
    queue_path = order.get("provided_order_path")
    queue_sha = sha((json.dumps(targets[:-1], indent=2) + "\n").encode())
    extras = set()
    if queue_path is not None:
        require(isinstance(queue_path, str) and Path(queue_path).is_absolute()
                and order.get("provided_order_file_sha256") == queue_sha, "Recorded source build queue provenance differs")
        queue_key = str(Path(queue_path).relative_to(root)) if Path(queue_path).is_relative_to(root) else queue_path
        extras.add(queue_key)
        require(input_map.get(queue_key) == queue_sha, "Actual build queue digest differs from raw run order")
    require(set(input_map) == required | extras
            and all(input_map.get(path) == hashes.get(path) for path in required),
            "Actual build must bind every940 source, pins and its exact build controls")
    require(build.get("source_sha256") == {m: hashes[m.replace(".", "/") + ".lean"] for m in modules},
            "Actual new-leaf source map differs from native audit")
    require(order.get("status") == "verified_actual_source_order_only"
            and order.get("library_module_count") == 930 + len(modules)
            and order.get("module_count") == len(modules) and order.get("order_sha256") == queue_sha
            and order.get("inventory_sha256") == hashes[INVENTORY]
            and order.get("aggregate_sha256") == hashes["BC4lean.lean"]
            and order.get("frozen_prefix_sha256") == PREFIX7_SHA
            and order.get("parser_sha256") == hashes["scripts/audit_chapter6.py"],
            "Actual aggregate library/source-order coverage differs")
    positions = {module: i for i, module in enumerate(targets[:-1])}
    edges, dependencies = 0, {}
    for module in modules:
        text = trusted.code_only(read(root, module.replace(".", "/") + ".lean").decode())
        deps = set(re.findall(r"(?m)^\s*import\s+(BC4lean(?:\.[\w']+)+)\s*$", text)) & set(modules)
        edges += len(deps); dependencies[module] = deps
        require(all(positions[dependency] < positions[module] for dependency in deps),
                "Actual native leaf order violates a current source dependency")
    require(order.get("internal_dependency_edges") == edges, "Actual source dependency-edge count differs")
    generated, remaining = [], {m: set(d) for m, d in dependencies.items()}
    while remaining:
        ready = sorted(m for m, deps in remaining.items() if not deps)
        require(ready, "Actual full-build dependency graph contains a cycle")
        module = ready[0]; generated.append(module); del remaining[module]
        for deps in remaining.values(): deps.discard(module)
    require(order.get("generated_order_sha256") == sha((json.dumps(generated, indent=2) + "\n").encode()),
            "Actual full-build generated source order differs")


def strict_recorded_command(stage, command, origin, output, query_sha, record):
    require(isinstance(command, list) and all(isinstance(a, str) for a in command), "Malformed recorded native command")
    lean = ["lake", "env", "lean", "-j1", "-DwarningAsError=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
    if stage == "build-gate":
        valid = command == ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"]
    elif stage == "retained-preservation":
        valid = len(command) == 9 and re.fullmatch(r"python(?:3(?:\.\d+)?)?", Path(command[0]).name) \
            and command[1:3] == ["-B", str(Path(origin) / RETAINED)] \
            and command[3:7] == ["--root", origin, "--new-inventory", INVENTORY] \
            and command[7] == "--output" and Path(command[8]).is_absolute() \
            and not Path(command[8]).is_relative_to(Path(origin))
    else:
        valid = len(command) == len(lean) + 1 and command[:-1] == lean
        if stage == "expected-types": valid = valid and command[-1] == str(Path(origin) / FIXTURE)
        elif stage == "kernel":
            valid = valid and command[-1] == str(output.with_suffix(".lean")) \
                and record.get("query_source_location") == str(output.with_suffix(".lean")) \
                and record.get("query_sha256") == query_sha
        else: valid = False
    require(bool(valid), "Recorded Chapter8 verification command is weakened or unrelated")


def recorded_locations(audit):
    origin = audit["source_root_provenance"]
    original_output = audit.get("audit_output_provenance")
    require(isinstance(original_output, str) and Path(original_output).is_absolute()
            and Path(original_output).suffix == ".json"
            and audit.get("query_source_location") == str(Path(original_output).with_suffix(".lean")),
            "Actual original audit output/query location provenance differs")
    require(isinstance(origin, str) and Path(origin).is_absolute()
            and ".." not in Path(origin).parts and str(Path(origin)) == origin,
            "Actual source root provenance must be an absolute canonical path")
    original_path = Path(original_output)
    require(".." not in original_path.parts and str(original_path) == original_output,
            "Original recorded audit output path has aliases")
    require(not original_path.is_relative_to(Path(origin))
            or original_path == Path(origin) / DIRECTORY / "audit.json",
            "Original recorded output violates the protected repository namespace")
    return origin, original_path


def verify_raw_evidence(root, output, audit, inventory, trusted):
    endpoints = inventory["intended_endpoints"]; links = audit["blueprint_links"]
    query = generate_query(inventory["modules"], links, endpoints, trusted).encode()
    require(bounded_file(sidecar(output, "lean")) == query and audit.get("query_sha256") == sha(query),
            "Chapter8 retained query is not the uncapped current inventory-generated census")
    records = {"retained-preservation": "retained_chapter7_preservation_run", "build-gate": "cached_strict_build_gate",
               "expected-types": "expected_types_run", "kernel": "kernel_run"}
    origin, original_output = recorded_locations(audit)
    previous_finish = None
    for stage, key in records.items():
        record = obj(bounded_file(sidecar(output, stage + "-run.json")), stage)
        raw = bounded_file(sidecar(output, stage + ".log"))
        require(record == audit.get(key) and type(record.get("exit_code")) is int and record["exit_code"] == 0
                and record.get("stdout_stderr_sha256") == sha(raw), "Raw native process record/log mismatch")
        start, finish = validate_process_record(record, stage, audit.get("run_id"), origin)
        require(previous_finish is None or start >= previous_finish, "Actual four verification processes overlap/reorder")
        previous_finish = finish
        strict_recorded_command(stage, record.get("command"), origin, Path(original_output), sha(query), record)
    retained_bytes = bounded_file(sidecar(output, "retained-preservation.json"))
    require(audit.get("retained_preservation_receipt_sha256") == sha(retained_bytes)
            and audit["retained_chapter7_preservation_run"].get("receipt_sha256") == sha(retained_bytes),
            "Actual retained Chapter7 receipt bytes are not bound to its subprocess")
    check_retained_receipt(obj(retained_bytes, "retained preservation"), inventory["modules"])
    parsed = parse_kernel(bounded_file(sidecar(output, "kernel.log")).decode(), inventory["modules"], links, endpoints,
                          {**inventory["required_declaration_kinds"], **inventory["blueprint_support_data_kinds"]}, trusted)
    require(all(audit.get(key) == value for key, value in parsed.items()), "Actual raw kernel evidence disagrees with audit")
    require(audit["expected_types_run"].get("source_sha256") == audit["source_sha256"][FIXTURE]
            and audit["expected_types_run"].get("fixture") == FIXTURE
            and audit["expected_type_examples"] == inventory["expected_type_examples"], "Independent fixture evidence differs")
    objects = audit.get("module_olean_sha256")
    required_objects = {".lake/build/lib/lean/" + m.replace(".", "/") + ".olean" for m in inventory["modules"]}
    require(isinstance(objects, dict) and required_objects <= set(objects)
            and all((path in required_objects or path.removesuffix(".private") in required_objects)
                    and isinstance(digest, str) and HASH.fullmatch(digest) for path, digest in objects.items()),
            "Actual native audit lacks exact compiled-object/private-object provenance")


def load_verified_audit(root, audit_path, source_revision, retained_provider=None):
    """Strict raw replay for new finder/site tools; never calls the old7 loader."""
    root = Path(root).resolve(); output = Path(audit_path).resolve()
    require(REV.fullmatch(source_revision), "Full immutable S8 is required")
    raw = bounded_file(output); audit = obj(raw, "native Chapter8 audit")
    require(audit.get("schema") == SCHEMA and audit.get("schema_version") == 1
            and audit.get("status") == "verified_milestone" and audit.get("milestone_verified") is True
            and audit.get("chapter_complete") is False and audit.get("general_conjecture_proved") is False
            and audit.get("source_revision") == source_revision and audit.get("module_sources_match_revision") is True
            and audit.get("inputs_unchanged_during_audit") is True, "No actual verified Chapter8 milestone evidence")
    hashes = audit.get("source_sha256")
    require(isinstance(hashes, dict) and set(CONTROLS) <= set(hashes) and len(hashes) <= 4096,
            "Audit lacks bounded current controls")
    for relative, expected in hashes.items():
        require(isinstance(expected, str) and HASH.fullmatch(expected) and sha(read(root, relative)) == expected,
                "Current source/control no longer matches native audit")
    # Verify tracked source provenance BEFORE executing the current provider.
    # No cached marker or caller-supplied provider is a proof of preservation.
    all_paths = sorted(hashes)
    committed = subprocess.run(["git", "ls-tree", "-r", "--name-only", source_revision, "--", *all_paths],
                               cwd=root, check=True, capture_output=True, text=True).stdout.splitlines()
    require(set(committed) == set(all_paths)
            and subprocess.run(["git", "diff", "--quiet", source_revision, "--", *all_paths], cwd=root).returncode == 0,
            "Current complete source/control snapshot differs from immutable audited S8")
    with retained_module(root) as provider:
        manifest = provider.load_manifest(read(root, BASELINE))
        current = provider.validate(provider.RepositoryReader(root), manifest, MODULES)
        if retained_provider is not None:
            require(retained_provider.audit_sha256 == current.audit_sha256
                    and retained_provider.locations == current.locations,
                    "Supplied retained provider differs from independent actual preservation")
        require(current.audit.get("source_revision") == SOURCE7 and current.receipt.get("proof_sources_preserved") == 930,
                "Missing actual retained proof preservation")
        inv = load_inventory(root / INVENTORY, read(root, INVENTORY))
        check_statement_definition_metadata(audit, inv)
        require(sha(read(root, FIXTURE)) == EXPECTED_TYPES_SHA,
                "Independent actual assembly/closed-Unit formula fixture lacks its reviewed binding")
        _, captured = capture(root, inv, provider)
        require(set(hashes) == set(captured), "Actual audit omitted a historical/current source binding")
        with current.helpers.open() as helpers:
            trusted = helpers["audit_chapter7"]
            links, targets, milestones = audit_blueprint(read(root, BLUEPRINT).decode(), inv, trusted)
            require(audit["modules"] == inv["modules"] and audit["blueprint_links"] == links
                    and audit["target_inventory"] == targets and audit["milestone_inventory"] == milestones,
                    "Current endpoint/source readiness differs from actual audit")
            require(targets["def:baum-connes-property"]["ready"] and not targets["conj:baum-connes"]["ready"]
                    and all(x["ready"] for x in milestones.values()), "Actual intended milestone endpoints incomplete")
            verify_raw_evidence(root, output, audit, inv, trusted)
            sources = {m: read(root, m.replace(".", "/") + ".lean").decode() for m in inv["modules"]}
            for module, source in sources.items(): check_sources(source, module, trusted)
            validate_fixture(read(root, FIXTURE), inv, trusted)
            require(audit["private_declaration_counts"] == trusted.check_private_coverage(sources, audit["declarations"]),
                    "Private/generated scope coverage differs")
            build_replay(root, obj(read(root, DIRECTORY + "/build.json"), "full build"),
                         read(root, DIRECTORY + "/build.log"), inv, hashes, trusted)
            require(audit.get("full_build_sha256") == sha(read(root, DIRECTORY + "/build.json"))
                    and audit.get("full_build_log_sha256") == sha(read(root, DIRECTORY + "/build.log")),
                    "Actual completed full-build evidence changed")
        paths = [m.replace(".", "/") + ".lean" for m in inv["modules"]]
        require(subprocess.run(["git", "diff", "--quiet", source_revision, "--", *paths], cwd=root).returncode == 0,
                "Current new proof sources differ from immutable S8")
    return audit, sha(raw)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--generate-only", action="store_true")
    mode.add_argument("--require-milestone", action="store_true")
    args = parser.parse_args(); root = args.root.resolve(strict=True)
    output = validate_output_scope(root, args.output or root / DIRECTORY / "audit.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    run_id = uuid.uuid4().hex
    # Invalidate any older passing output before a new preflight can fail.
    write_json(output, {"schema": SCHEMA, "schema_version": 1, "run_id": run_id,
                        "status": "verification_not_started", "milestone_verified": False,
                        "chapter_complete": False, "general_conjecture_proved": False})
    inventory = load_inventory(root / INVENTORY, read(root, INVENTORY))
    with retained_module(root) as provider:
        manifest, captured = capture(root, inventory, provider)
        require(sha(captured[FIXTURE]) == EXPECTED_TYPES_SHA,
                "Independent fixture changed; retain actual property/general/closed Unit formulas and re-review")
        reader = provider.RepositoryReader(root)
        helper_sources = provider.verified_helper_sources(reader, manifest)
        hashes = {path: sha(data) for path, data in captured.items()}
        with helper_sources.open() as helpers:
            trusted = helpers["audit_chapter7"]
            links, targets, milestones = audit_blueprint(captured[BLUEPRINT].decode(), inventory, trusted)
            for module in inventory["modules"]:
                check_sources(captured[module.replace(".", "/") + ".lean"].decode(), module, trusted)
            validate_fixture(captured[FIXTURE], inventory, trusted)
            require(sha(captured[IMPORTS]) == PREFIX7_SHA and captured["BC4lean.lean"].startswith(captured[IMPORTS]),
                    "Frozen930 aggregate prefix changed")
            provider.verify_extensions(captured["BC4lean.lean"], captured[IMPORTS], reader.proof_paths(),
                                       set(manifest["proof_sources"]), inventory["modules"])
            query = generate_query(inventory["modules"], links, inventory["intended_endpoints"], trusted).encode()
        query_path = sidecar(output, "lean"); query_path.write_bytes(query)
        revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, check=True, capture_output=True, text=True).stdout.strip()
        paths = sorted(captured)
        tracked = subprocess.run(["git", "ls-files", "--error-unmatch", "--", *paths], cwd=root, capture_output=True)
        unchanged = subprocess.run(["git", "diff", "--quiet", revision, "--", *paths], cwd=root)
        evidence = {"run_id": run_id, "audit_started_utc": utc_now(), "schema": SCHEMA, "schema_version": 1, "status": "generated_only", "milestone_verified": False,
                    "chapter_complete": False, "general_conjecture_proved": False,
                    "source_revision": revision, "source_root_provenance": str(root),
                    "audit_output_provenance": str(output), "query_source_location": str(query_path),
                    "module_sources_match_revision": tracked.returncode == unchanged.returncode == 0,
                    "modules": inventory["modules"], "source_modules": inventory["modules"],
                    "source_sha256": hashes, "query_sha256": sha(query), "blueprint_links": links,
                    "target_inventory": targets, "milestone_inventory": milestones,
                    "statement_definition_declarations": inventory["statement_definition_declarations"],
                    "notready_targets": ["conj:baum-connes"], "expected_type_examples": inventory["expected_type_examples"]}
        write_json(sidecar(output, "inputs.json"), evidence); write_json(output, evidence)
        if args.generate_only:
            print("Generated only; no native milestone or conjecture proof acceptance."); return 0
        try:
            with compiler_lock(root, output, run_id) as lease:
                require(REV.fullmatch(revision) and evidence["module_sources_match_revision"] is True,
                        "Native audit acceptance requires the complete committed immutable S8 source snapshot")
                build_bytes, build_log = read(root, DIRECTORY + "/build.json"), read(root, DIRECTORY + "/build.log")
                with helper_sources.open() as helpers:
                    build_replay(root, obj(build_bytes, "full build"), build_log, inventory, hashes, helpers["audit_chapter7"])
                evidence["full_build_sha256"], evidence["full_build_log_sha256"] = sha(build_bytes), sha(build_log)
                objects = {".lake/build/lib/lean/" + m.replace(".", "/") + ".olean" for m in inventory["modules"]}
                objects |= {p + ".private" for p in list(objects) if (root / (p + ".private")).is_file()}
                object_hashes = {path: sha(read(root, path)) for path in sorted(objects)}
                evidence["current_import_coverage"] = current_import_check(root, captured["scripts/check_project_imports.py"])
                with tempfile.TemporaryDirectory(prefix="chapter8-retained-actual-") as temporary:
                    retained_path = Path(temporary) / "receipt.json"
                    command = [sys.executable, "-B", str(root / RETAINED), "--root", str(root),
                               "--new-inventory", INVENTORY, "--output", str(retained_path)]
                    run, _ = run_process(root, command, output, "retained-preservation", lease, run_id)
                    retained_bytes = retained_path.read_bytes()
                    check_retained_receipt(obj(retained_bytes, "actual retained preservation"), inventory["modules"])
                    sidecar(output, "retained-preservation.json").write_bytes(retained_bytes)
                    run["receipt_sha256"] = sha(retained_bytes)
                    write_json(sidecar(output, "retained-preservation-run.json"), run)
                    evidence["retained_chapter7_preservation_run"] = run
                    evidence["retained_preservation_receipt_sha256"] = sha(retained_bytes)
                gate, _ = run_process(root, ["lake", "--wfail", "--no-build", "--no-cache", "build", "BC4lean"], output, "build-gate", lease, run_id)
                lean = ["lake", "env", "lean", "-j1", "-DwarningAsError=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false"]
                types_run, _ = run_process(root, lean + [str(root / FIXTURE)], output, "expected-types", lease, run_id,
                                           fixture=FIXTURE, source_sha256=hashes[FIXTURE])
                require(sha(query_path.read_bytes()) == sha(query), "Census query changed before real kernel run")
                kernel, stdout = run_process(root, lean + [str(query_path)], output, "kernel", lease, run_id, query_sha256=sha(query),
                                               query_source_location=str(query_path))
                with helper_sources.open() as helpers:
                    trusted = helpers["audit_chapter7"]
                    evidence.update(parse_kernel(stdout.decode(), inventory["modules"], links, inventory["intended_endpoints"],
                                                 {**inventory["required_declaration_kinds"], **inventory["blueprint_support_data_kinds"]}, trusted))
                    sources = {m: captured[m.replace(".", "/") + ".lean"].decode() for m in inventory["modules"]}
                    evidence["private_declaration_counts"] = trusted.check_private_coverage(sources, evidence["declarations"])
                for path, expected in {**hashes, **object_hashes}.items():
                    require(sha(read(root, path)) == expected, "Actual audit input/object changed during verification")
                require(sha(query_path.read_bytes()) == sha(query), "Generated metadata changed during native verification")
                require(sha(read(root, DIRECTORY + "/build.json")) == sha(build_bytes)
                        and sha(read(root, DIRECTORY + "/build.log")) == sha(build_log),
                        "Full actual build reports changed during native audit")
                require(reader.proof_paths() == set(manifest["proof_sources"]) | {m.replace(".", "/") + ".lean" for m in inventory["modules"]},
                        "Actual full proof-path set changed during verification")
                ready = targets["def:baum-connes-property"]["ready"] and all(x["ready"] for x in milestones.values())
                evidence.update({"status": "verified_milestone" if ready else "verified_partial_metadata", "milestone_verified": bool(ready),
                                 "inputs_unchanged_during_audit": True, "audit_finished_utc": utc_now(), "module_olean_sha256": object_hashes,
                                 "cached_strict_build_gate": gate, "expected_types_run": types_run, "kernel_run": kernel})
        except (OSError, ValueError, RuntimeError, KeyError) as error:
            evidence.update(status="verification_failed", milestone_verified=False, failure=str(error))
            write_json(output, evidence); raise
        write_json(output, evidence)
        print(f"Actual Chapter8 metadata census: {evidence['declaration_count']} declarations; general conjecture remains unproved.")
        return 2 if args.require_milestone and not evidence["milestone_verified"] else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Chapter8 audit rejected: {error}", file=sys.stderr)
        raise SystemExit(1)
