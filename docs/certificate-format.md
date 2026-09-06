# Certificate format

`schemas/descent-certificate-v1.json` specifies a finite record with start,
steps, and target. Consumers must recompute the trajectory before accepting
semantic interpretation. Schema versions are immutable.

The v1.0 digest is the SHA-256 of the canonical JSON bytes for the
proof-bearing fields: `schema_version`, `start`, `steps`, and `target`. The
digest is not embedded in the v1.0 record; embedded `digest` fields are rejected
as unknown fields. The checker returns the recomputed digest and can compare it
with an external expected digest.
