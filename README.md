# zify-tests
Tests on the zify tactic

In the `coq-tests` directory:
- `abstract_integer_type.v`: first tests on an abstract integer type (addition, equality);
- `ssrint_type.v`: tests on the `ssrint` type;
- `ring_operations.v`: tests with the ring notations and generic operations;
- `smtcoq_after_zify.v`: copies of some outputs of `zify` given to the SMTCoq `smt` tactic, to check whether the goals can be solved easily;
- `uninterpreted.v`: some tests on uninterpreted values.

In the `translation-algorithm` directory:
- `translation.ml`: an OCaml algorithm to translate `bool` to `Prop` and various integer types to `Z` in goals expressed in a simplified model of Coq's types, and with uninterpreted values.