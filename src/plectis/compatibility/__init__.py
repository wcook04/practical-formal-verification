"""Preserve every admitted observation of a finite deterministic model.

``compare`` searches for the first shortest differing input continuation. An
accepted relation is checked by Python generated from the proved Dafny checker.
A continuation is returned only when the generated verdict checker accepts it
as a real difference with none shorter and none earlier in sorted input order.
The search itself is unproved and replaceable. The model parser, the encoding,
and correspondence to real programs are trusted.
"""

from ._api import InvalidMachine, check_certificate, check_counterexample, compare

__all__ = ["InvalidMachine", "check_certificate", "check_counterexample", "compare"]
