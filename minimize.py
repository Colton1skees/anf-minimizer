# Ignore some deprecration warnings coming from using z3
import warnings
warnings.filterwarnings("ignore", message="pkg_resources is deprecated as an API", category=UserWarning)

import time
from bitwuzla import *
from smt_wrapper import *

tm = SmtWrapper()

# TODO:
# - Use weighted MaxSAT instead of the bitvector based cost function
# - Formulate problem as multivariate interpolation in gf2 (it kind of already is); Do GJE over system. ANF->CNF conversion using bosphorus. 
# - ILP formulation?
# - Use Boolsort instead of BitVec
# TODO: Enumerate through all NPN transformations and check which version has the sparsest and densest truth table.
# They will probably have a more compact or-xor form. 
DEFAULT_MAX_COST = 10
# Variable permuting is disabled for now,
# because it slows things down and (I think) cannot improve the result quality.
PERMUTE_VARIABLES = False
class Minimizer():
    def __init__(self, variables, circuit, num_connectors, npn_optimal = False, use_optimizer = False, max_cost = None):
        # Bitwuzla doesn't have an optimizer like z3, so we ignore use_optimizer
        self.use_optimizer = False  # Not supported in bitwuzla
        self.variables = variables
        self.circuit = circuit
        self.num_connectors = num_connectors
        self.npn_optimal = npn_optimal
        self.max_cost = DEFAULT_MAX_COST if max_cost is None else max_cost

    def minimize(self):
        # Create a synth template
        monomials = self.get_all_monomials()
        template_circuit, coefficients, connectors = self.get_synth_template(monomials)

        # Assert that both circuits are equivalent
        self.add_equivalence_constraint(template_circuit)

        # Use the number of literal occurrences in each monomial as a cost function
        sum_size = 16
        cost = tm.bvalue(0, sum_size)
        for c, i in coefficients:
            popcount = 1 if i == 0 else i.bit_count()
            cost = tm.add(cost, tm.ite(c, tm.bvalue(popcount, sum_size), tm.bvalue(0, sum_size)))
        
        # Add cost constraint
        max_cost_val = tm.bvalue(self.max_cost, sum_size)
        tm.assert_formula(tm.ult(cost, max_cost_val))

        
        result = tm.check_sat()
        if result != Result.SAT:
            raise Exception(f"Solution with cost < {self.max_cost} does not exist!")

        solution_str = self.get_solution_str(tm.solver, coefficients)
        cost_val = int(tm.solver.get_value(tm.unwrap(cost)).value(), 2)
        return (solution_str, cost_val)
                
    # Compute a list of all 2**t possible monomials
    def get_all_monomials(self):
        monomials = []
        for i in range(2**len(self.variables)):
            if i == 0:
                monomials.append(tm.bvalue(1, 1))
                continue

            m = tm.bvalue(1, 1)
            for vidx in range(len(self.variables)):
                if i & (1 << vidx) == 0:
                    continue
                m = tm.land(m, self.variables[vidx])

            monomials.append(m)
        return monomials
    
    def get_synth_template(self, monomials):
        coefficients = []
        template_circuit = tm.bvalue(0, 1)
        connectors = []
        for _ in range(self.num_connectors):
            # Generate an ANF poly with unknown coefficients
            poly = tm.bvalue(0, 1)
            for i, m in enumerate(monomials):
                c = tm.bv(f'c{len(coefficients)}', 1)
                coefficients.append((c, i))

                poly = tm.lxor(poly, tm.land(c, m))
            
            template_circuit = tm.lor(template_circuit, poly)
            connectors.append(poly)
        return template_circuit, coefficients, connectors
    
    def add_equivalence_constraint(self, template_circuit):
        n = len(self.variables)
        
        # If npn_optimal is enabled, we need to consider:
        #   - All permutations of variable orderings
        #   - All permutations of variable negations
        #   - Negation of the output
        var_negators = [tm.bv(f'var_neg_{i}', 1) if self.npn_optimal else tm.bvalue(0, 1) for i in range(n)]
        var_permutors = [tm.bv(f'var_perm_{i}', n) if self.npn_optimal and PERMUTE_VARIABLES else tm.bvalue(i, n) for i in range(n)]
        
        if self.npn_optimal:
            tm.assert_formula(tm.distinct(var_permutors))
            for v in var_permutors:
                tm.assert_formula(tm.ult(v, tm.bvalue(n, n)))

        output_negator = tm.bv('output_neg', 1) if self.npn_optimal else tm.bvalue(0, 1)
        for i in range(2**n):
            template_subst_map = []
            for vidx in range(n):
                val = tm.bvalue((i >> vidx) & 1, 1)
                template_subst_map.append((self.variables[vidx], val))

            circuit_subst_map = []
            for vidx in range(n):
                i_bv = tm.bvalue(i, n)
                shifted = tm.lshr(i_bv, var_permutors[vidx])
                bit = tm.extract(0, 0, shifted)
                
                val = tm.lxor(bit, var_negators[vidx])
                circuit_subst_map.append((self.variables[vidx], val))

            # Evaluate both circuits on the ith input combination and assert their equivalence
            eval0 = tm.substitute(template_circuit, template_subst_map)
            eval1 = tm.lxor(tm.substitute(self.circuit, circuit_subst_map), output_negator)
            tm.assert_formula(tm.eq(eval0, eval1))

    def get_solution_str(self, bitwuzla, coefficients):
        ci = 0
        products = []
        for _ in range(self.num_connectors):
            terms = []
            for i in range(2**len(self.variables)):
                coeff = coefficients[ci][0]
                ci += 1

                coeff_val = int(bitwuzla.get_value(tm.unwrap(coeff)).value(), 2)

                if coeff_val == 0:
                    continue

                monomial_str = "*".join([f"x{j}" for j in range(len(self.variables)) if (i & (1 << j)) != 0])
                if i == 0:
                    monomial_str = "1"

                terms.append(monomial_str)

            products.append(" + ".join(terms))

        return '|'.join([f"({p})" for p in products if p != ""])

def get_n_vars(n):
    vars = [tm.bv(f'x{i}', 1) for i in range(n)]
    return vars

def case0():
    vars = get_n_vars(2)
    (x0, x1) = vars
    circuit = x0^x1
    return vars, circuit, 2

def case1():
    x = get_n_vars(5)
    circuit = x[0]|x[1]|x[2]|x[3]|x[4]
    return x, circuit, 6

def case2():
    vars = get_n_vars(4)
    (t, y, z, x) = vars
    circuit = ~((((((((((t&y)&x)^(y&x))^(z&y))^(t&x))^(t&y))^(t&z))^x)^z)|((((((z&x)^(z&y))^(t&x))^(t&y))^(t&z))^z))
    return vars, circuit, 4, 11 # cost assumes npn opt is turned on

def case3():
    vars = get_n_vars(5)
    (a, b, c, d, e) = vars
    circuit = (~(((((a^b)^c)^(d&((((a^b)^c)^(e&(((a^b)^c)^(bvalue(0,1)&((a^b)^c)))))^(bvalue(0,1)&((a^b)^c)))))^(e&(((a^b)^c)^(bvalue(0,1)&((a^b)^c)))))^(bvalue(0,1)&((a^b)^c))))^(~a&~b&~c&~d&~e)
    return vars, circuit, 5

def case4():
    vars = get_n_vars(4)
    (x0, x1, x2, x3) = vars
    circuit = ~((~((x1 & x0) ^ (x3 & x2) ^ x0 ^ x1 ^ x2)) | (x2 & (x0 ^ x3)) | (x2 & (x1 ^ x3)) | (~x3 & (~(x0 ^ x2))) | (~x3 & (~(x1 ^ x2))))
    return vars, circuit, 4

def case5():
    vars = get_n_vars(5)
    (a, b, c, d, e) = vars
    circuit = (~(((((((((((c^(e&((c^b)^a)))^(d&(((c^(e&((c^b)^a)))^b)^a)))^b)^a)|(b&(one^(e^(c&(one^e))))))|(((d&(((e&(one^(c^b)))^c)^b))^(e&c))^(a&(one^(((e^d)^c)^(b&(one^e)))))))|((c&(one^(d^(a&(one^d)))))^(b&(one^(e^(d&(one^e)))))))|((((e^(d&(e^a)))^(c&(one^(e^(d&(one^e))))))^(b&(((e^(d&(one^e)))^c)^(a&(one^c)))))^a))|(d&((e^(c&e))^(b&(one^c)))))|((((e^(d&(((e^(c&(one^e)))^b)^(a&(one^b)))))^(c&(one^e)))^b)^(a&(one^b))))|(((((d&((((e&(one^(c^b)))^c)^b)^a))^c)^b)^(e&(b^(a&(one^c)))))^a)))
    return vars, circuit, 5, 30

def case6():
    vars = get_n_vars(5)
    (a, b, c, d, e) = vars
    circuit = (~(((((((((((((e&(-1^(b^a)))^(d&((((e&(-1^(b^a)))^c)^b)^a)))^c)^b)^a)|((((e&(-1^c))^d)^(c&d))^(a&(-1^(e^(b&(-1^e)))))))|(((e^(d&e))^(c&(-1^d)))^(b&((d&(-1^e))^(c&(-1^e))))))|((((d^(e&(((d^c)^(b&(-1^d)))^(a&(-1^c)))))^c)^(b&(-1^d)))^(a&(-1^c))))|((((e^(d&(-1^e)))^c)^(b&(((e^(d&(-1^e)))^c)^(a&(-1^c)))))^(a&(-1^c))))|((((e^(d&(((e^c)^(b&(-1^e)))^(a&(-1^c)))))^c)^(b&(-1^e)))^(a&(-1^c))))|(((e^(d&e))^(c&(-1^d)))^(b&((e^(d&e))^(c&(-1^d))))))|(((e^(d&e))^(b&(e&(-1^d))))^(a&(-1^(d^(b&(-1^d)))))))|(e&(-1^(d^(c&(-1^d))))))) 
    return vars, circuit, 5, 24

def case_readme():
    vars = get_n_vars(5)
    (x0, x1, x2, x3, x4) = vars
    circuit = (x3 & (1 ^ x0 ^ x1 ^ x2)) | (x4 & (x0 ^ x1 ^ x2 ^ x3)) | (x2 & x3 & (x0 ^ x1)) | x3
    return vars, circuit, 5, 8, 20

def case_ideal():
    vars = get_n_vars(5)
    (x0, x1, x2, x3, x4) = vars
    
    ideal = [
        x1&x3 ^ x0&x1&x3 ^ x1&x2&x3,
        x2&x3 ^ x0&x1&x4 ^ x2&x4,
        x2&x3 ^ x1&x2&x3 ^ x0&x3&x4,
        x1&x2 ^ x0&x1&x2 ^ x1&x2&x3
    ]

    # 0,3 has cost 8
    circuit = ideal[0]|ideal[3]

    return vars, circuit, 2, 9, 20

case = case0()
variables, circuit, num_connectors, max_cost = (case[0], case[1], case[2], None if len(case) < 4 else case[3])
minimizer = Minimizer(variables, circuit, num_connectors, npn_optimal = True, max_cost = max_cost)
start_time = time.perf_counter()
(solution, cost) = minimizer.minimize()
end_time = time.perf_counter()
print(f"Found solution: {solution} with cost: {cost}. Took {(end_time - start_time) * 1000} ms" )