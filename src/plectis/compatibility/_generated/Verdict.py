import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Compatibility as Compatibility
import Replay as Replay

# Module: Verdict

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Shape(approved, candidate, labels):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                d_1_t_: int = forall_var_1_
                return not (((0) <= (d_1_t_)) and ((d_1_t_) < (len((labels)[d_0_s_])))) or ((default__.Never) <= (((labels)[d_0_s_])[d_1_t_]))

            d_0_s_: int = forall_var_0_
            return not (((0) <= (d_0_s_)) and ((d_0_s_) < (len(labels)))) or (((len((labels)[d_0_s_])) == (len((candidate).next_))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((labels)[d_0_s_])), True, lambda1_)))

        return ((len(labels)) == (len((approved).next_))) and (_dafny.quantifier(_dafny.IntegerRange(0, len(labels)), True, lambda0_))

    @staticmethod
    def DiffersNow(approved, candidate, s, t, a):
        return (((((candidate).next_)[t])[a]) < (0)) or (((((approved).output)[s])[a]) != ((((candidate).output)[t])[a]))

    @staticmethod
    def LabelsHold(approved, candidate, labels):
        def lambda0_(forall_var_0_):
            def lambda1_(forall_var_1_):
                def lambda2_(forall_var_2_):
                    d_2_a_: int = forall_var_2_
                    return not ((((((0) <= (d_0_s_)) and ((d_0_s_) < (len((approved).next_)))) and (((0) <= (d_1_t_)) and ((d_1_t_) < (len((candidate).next_))))) and (((0) <= (d_2_a_)) and ((d_2_a_) < ((approved).inputs)))) and ((0) <= ((((approved).next_)[d_0_s_])[d_2_a_]))) or ((((0) <= (((labels)[d_0_s_])[d_1_t_])) and ((((labels)[d_0_s_])[d_1_t_]) <= (1)) if default__.DiffersNow(approved, candidate, d_0_s_, d_1_t_, d_2_a_) else ((((labels)[(((approved).next_)[d_0_s_])[d_2_a_]])[(((candidate).next_)[d_1_t_])[d_2_a_]]) == (default__.Never) if (((labels)[d_0_s_])[d_1_t_]) == (default__.Never) else ((((labels)[(((approved).next_)[d_0_s_])[d_2_a_]])[(((candidate).next_)[d_1_t_])[d_2_a_]]) == (default__.Never)) or ((((labels)[d_0_s_])[d_1_t_]) <= ((1) + (((labels)[(((approved).next_)[d_0_s_])[d_2_a_]])[(((candidate).next_)[d_1_t_])[d_2_a_]]))))))

                d_1_t_: int = forall_var_1_
                return _dafny.quantifier(_dafny.IntegerRange(0, (approved).inputs), True, lambda2_)

            d_0_s_: int = forall_var_0_
            return _dafny.quantifier(_dafny.IntegerRange(0, len((candidate).next_)), True, lambda1_)

        return (default__.Shape(approved, candidate, labels)) and (_dafny.quantifier(_dafny.IntegerRange(0, len((approved).next_)), True, lambda0_))

    @staticmethod
    def SmallerInputsRuledOut(approved, candidate, labels, s, t, first, remaining):
        def lambda0_(forall_var_0_):
            d_0_a_: int = forall_var_0_
            return not ((((0) <= (d_0_a_)) and ((d_0_a_) < (first))) and ((0) <= ((((approved).next_)[s])[d_0_a_]))) or ((not(default__.DiffersNow(approved, candidate, s, t, d_0_a_))) and (((((labels)[(((approved).next_)[s])[d_0_a_]])[(((candidate).next_)[t])[d_0_a_]]) == (default__.Never)) or ((remaining) <= (((labels)[(((approved).next_)[s])[d_0_a_]])[(((candidate).next_)[t])[d_0_a_]]))))

        return _dafny.quantifier(_dafny.IntegerRange(0, first), True, lambda0_)

    @staticmethod
    def FirstWord(approved, candidate, labels, s, t, word):
        while True:
            with _dafny.label():
                if ((((len(word)) == (0)) or (((word)[0]) < (0))) or (((approved).inputs) <= ((word)[0]))) or (((((approved).next_)[s])[(word)[0]]) < (0)):
                    return False
                elif not(default__.SmallerInputsRuledOut(approved, candidate, labels, s, t, (word)[0], len(word))):
                    return False
                elif default__.DiffersNow(approved, candidate, s, t, (word)[0]):
                    return (len(word)) == (1)
                elif True:
                    in0_ = approved
                    in1_ = candidate
                    in2_ = labels
                    in3_ = (((approved).next_)[s])[(word)[0]]
                    in4_ = (((candidate).next_)[t])[(word)[0]]
                    in5_ = _dafny.SeqWithoutIsStrInference((word)[1::])
                    approved = in0_
                    candidate = in1_
                    labels = in2_
                    s = in3_
                    t = in4_
                    word = in5_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Check(approved, candidate, labels, verdict):
        def lambda0_():
            source0_ = verdict
            if True:
                if source0_.is_Compatible:
                    return (((labels)[(approved).initial])[(candidate).initial]) == (default__.Never)
            if True:
                d_0_word_ = source0_.word
                return ((((labels)[(approved).initial])[(candidate).initial]) == (len(d_0_word_))) and (default__.FirstWord(approved, candidate, labels, (approved).initial, (candidate).initial, d_0_word_))

        return ((Replay.default__.ValidPair(approved, candidate)) and (default__.LabelsHold(approved, candidate, labels))) and (lambda0_())

    @_dafny.classproperty
    def Never(instance):
        return -1

class Verdict:
    @classmethod
    def default(cls, ):
        return lambda: Verdict_Compatible()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Compatible(self) -> bool:
        return isinstance(self, Verdict_Compatible)
    @property
    def is_Differs(self) -> bool:
        return isinstance(self, Verdict_Differs)

class Verdict_Compatible(Verdict, NamedTuple('Compatible', [])):
    def __dafnystr__(self) -> str:
        return f'Verdict.Verdict.Compatible'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Verdict_Compatible)
    def __hash__(self) -> int:
        return super().__hash__()

class Verdict_Differs(Verdict, NamedTuple('Differs', [('word', Any)])):
    def __dafnystr__(self) -> str:
        return f'Verdict.Verdict.Differs({_dafny.string_of(self.word)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Verdict_Differs) and self.word == __o.word
    def __hash__(self) -> int:
        return super().__hash__()

