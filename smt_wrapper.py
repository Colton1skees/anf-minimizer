from bitwuzla import *
# Wrapper around bitwuzla to avoid being tightly coupled to one specific solver.
# Ideally we could swap out bitwuzla for a portfolio of different solvers.
class SmtWrapper:
    def __init__(self):
        self.tm = TermManager()
        options = Options()
        options.set(Option.PRODUCE_MODELS, True)
        self.solver = Bitwuzla(self.tm, options)

    def unwrap(self, term):
        if isinstance(term, BV):
            return term._term
        return term
    
    def mkbv(self, t):
        return BV(self.tm, t)

    def bv(self, name, size):
        return self.mkbv(self.tm.mk_const(self.bv_sort(size), name))

    def bvalue(self, val, size):
        return self.mkbv(self.tm.mk_bv_value(self.bv_sort(size), val))
    
    def ite(self, cond, then_val, else_val):
        one = self.tm.mk_bv_value(self.bv_sort(1), 1)
        bool_cond = self.tm.mk_term(Kind.EQUAL, [self.unwrap(cond), one])
        return self.mkbv(self.tm.mk_term(Kind.ITE, [bool_cond, self.unwrap(then_val), self.unwrap(else_val)]))

    def ult(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_ULT, [self.unwrap(a), self.unwrap(b)]))

    def distinct(self, *args):
        if len(args) == 1 and isinstance(args[0], list):
            args = args[0]
        return self.mkbv(self.tm.mk_term(Kind.DISTINCT, [self.unwrap(a) for a in args]))

    def lshr(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_SHR, [self.unwrap(a), self.unwrap(b)]))

    def extract(self, high, low, term):
        return self.mkbv(self.tm.mk_term(Kind.BV_EXTRACT, [self.unwrap(term)], [high, low]))

    def substitute(self, term, subst_list):
        subst_map = {self.unwrap(old): self.unwrap(new) for old, new in subst_list}
        return self.mkbv(self.tm.substitute_term(self.unwrap(term), subst_map))

    def lxor(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_XOR, [self.unwrap(a), self.unwrap(b)]))

    def land(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_AND, [self.unwrap(a), self.unwrap(b)]))

    def lor(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_OR, [self.unwrap(a), self.unwrap(b)]))
    
    def eq(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.EQUAL, [self.unwrap(a), self.unwrap(b)]))
    
    def add(self, a, b):
        return self.mkbv(self.tm.mk_term(Kind.BV_ADD, [self.unwrap(a), self.unwrap(b)]))

    def bv_sort(self, size):
        return self.tm.mk_bv_sort(size)
    
    def assert_formula(self, formula):
        self.solver.assert_formula(self.unwrap(formula))

    def check_sat(self):
        return self.solver.check_sat()
    
class BV:
    def __init__(self, tm, term):
        self.tm = tm
        if isinstance(term, BV):
            self._term = term._term
        else:
            self._term = term
    
    @property
    def term(self):
        return self._term
    
    def _wrap(self, other):
        if isinstance(other, BV):
            return other._term
        elif isinstance(other, int):
            return self.tm.mk_bv_value(self.tm.mk_bv_sort(1), other & 1)
        else:
            return other
    
    def __or__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_OR, [self._term, self._wrap(other)]))
    
    def __ror__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_OR, [self._wrap(other), self._term]))
    
    def __and__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_AND, [self._term, self._wrap(other)]))
    
    def __rand__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_AND, [self._wrap(other), self._term]))
    
    def __xor__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_XOR, [self._term, self._wrap(other)]))
    
    def __rxor__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_XOR, [self._wrap(other), self._term]))
    
    def __invert__(self):
        return BV(self.tm, self.tm.mk_term(Kind.BV_NOT, [self._term]))
    
    def __add__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_ADD, [self._term, self._wrap(other)]))
    
    def __radd__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_ADD, [self._wrap(other), self._term]))
    
    def __sub__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_SUB, [self._term, self._wrap(other)]))
    
    def __rsub__(self, other):
        return BV(self.tm, self.tm.mk_term(Kind.BV_SUB, [self._wrap(other), self._term]))
    
    def __repr__(self):
        return f"BV({self._term})"