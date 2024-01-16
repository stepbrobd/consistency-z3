import z3


def compatible(s1: z3.Solver, s2: z3.Solver, verbose=False) -> bool:
    """
    Check if all assertions in s2 are satisfiable in s1.
    True means s2 is compatible with s1.
    False means s2 is incompatible with s1.
    Note: if a system S_1 provide guarantee G_1, another system S_2 provide guarantee G_2,
    `compatible(G_1, G_2) == True` means:
    the service mesh of S_1 and S_2 can be composed to provide at a guarantee of G_1,
    i.e. all assertions in G_2 are satisfied in G_1.
    Also, compatibility is not symmetric
    i.e. if mr is compatible with ryw, then ryw is not necessarily compatible with mr.
    """
    if verbose:
        z3.set_param("verbose", 10)

    s = z3.Solver()

    lhs = z3.And(*set(s1.assertions()))
    rhs = z3.And(*set(s2.assertions()))

    s.add(z3.Not(z3.Implies(lhs, rhs)))

    return s.check() == z3.unsat
