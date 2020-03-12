# zify-tests
Tests on the zify tactic

- `zify_simple.v`: tests on a virtual integer type;
- `zify.v`: tests on the `ssrint` type;
- `ring_zify.v`: tests with the ring notations and generic operations;
- `smtcoq_after_zify.v`: copies of the outputs of `zify` given to the SMTCoq `smt` tactic to check whether the goals can be solved.