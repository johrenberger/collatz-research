"""Certificate data structures. Validation does not confer proof status."""

from dataclasses import asdict, dataclass

from .trajectory import iterate


@dataclass(frozen=True, slots=True)
class DescentCertificate:
    schema_version: str
    start: int
    steps: int
    target: int

    def as_dict(self) -> dict[str, int | str]:
        return asdict(self)


def build_descent_certificate(start: int, steps: int) -> DescentCertificate:
    """Generate a finite accelerated-trajectory certificate.

    This is an untrusted generator. Consumers must route the result through
    the checker before treating it as an accepted finite certificate.
    """
    target = list(iterate(start, steps))[-1]
    return DescentCertificate("1.0", start, steps, target)
