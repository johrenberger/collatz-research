"""Run lightweight, dependency-free sanity checks for a fresh checkout."""

from collatz_research.accelerated import accelerated_step


def main() -> None:
    assert accelerated_step(3) == 5
    print("Python arithmetic smoke check passed.")


if __name__ == "__main__":
    main()
