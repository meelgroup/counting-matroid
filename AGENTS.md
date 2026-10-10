# Inspection failure diagnosis (2026-10-08)

The legacy Tex2Lean host can report `Lean completed without writing its
inspection record` even when Lean wrote the record successfully. This run's
full inspection JSON was 540,044,936 bytes; Node's maximum string length is
536,870,888. Decoding the record throws `ERR_STRING_TOO_LONG`, which the old
host incorrectly reports as a missing record. Repeated complete `lake build`
checks passed, and an independent full compiler inspection wrote its record.

Tex2Lean 1.0.1 has a verified fix: bounded inspection-record chunks preserving
all 2,523 declaration fingerprints exactly. The package is installed; the
existing VS Code extension host needs a window reload to activate it.

When the build passes and this same missing-record error repeats, include this
host-side diagnosis in the report. The error alone does not establish a broken
proof, missing project import, or faulty audit. Require concrete compiler
errors before changing project declarations for this failure. Preserve prior
attempts and all development work; do not undo, reset, restore, revert, clean,
stash, or replace project files from Git or by a substitute rollback mechanism.
