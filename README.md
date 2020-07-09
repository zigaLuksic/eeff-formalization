# Formalisation of EEFF

This repository contains the formalisation of the programming language EEFF.

The three branches are
- *master*: contains the formalisation of EEFF with predicate logic
- *equational-logic*: contains the formalisation of EEFF with equational logic
- *bidirectional*: contains the formalisation of the bidirectional type inference


All files contain `Add LoadPath` commands with the relative paths prefixed by `???` to allow a search-and-replace with the absolute path of the repository.

# Predicate Logic

To verify correctness of bidirectional inference the order of compilation is:
1. `syntax/syntax.v`
2. `substitution/substitution.v`
3. `type_system/subtyping.v`
4. `type_system/declarational.v`
5. `bidirectional/bidirectional.v`
6. `bidirectional/erasure.v`

To verify correctness of the annotation-less declarational type system the order of compilation is:
1. `syntax/syntax.v`
2. `syntax/syntax_lemmas.v`
3. `substitution/substitution.v`
4. `substitution/substitution_lemmas.v`
5. `operational_semantics/operational_semantics.v`
6. `type_system/subtyping.v`
7. `type_system/declarational.v`
8. `type_system/wf_lemmas.v`
9. `type_system/subtyping_lemmas.v`
10. `type_system/type_aux_lemmas.v`
11. `type_system/type_lemmas.v`

Locations of important proofs:
- **Correctness of inference** is located in `bidirectional/erasure.v`.
- **Substitution lemmas** are located in `type_system/type_aux_lemmas.v`.
- **Safety** is located in `type_system/type_lemmas.v`.