# Formalisation of EEFF

This repository contains the formalisation of the programming language EEFF.

The three branches are
- *master*: contains the formalisation of EEFF with predicate logic
- *equational-logic*: contains the formalisation of EEFF with equational logic
- *bidirectional*: contains the formalisation of the bidirectional type inference


All files contain `Add LoadPath` commands with the relative paths prefixed by `???` to allow a search-and-replace with the absolute path of the repository.

# Equational Logic

The order of compilation is:
1. `syntax/syntax.v`
2. `syntax/syntax_lemmas.v`
3. `substitution/substitution.v`
4. `substitution/substitution_lemmas.v`
5. `operational_semantics/operational_semantics.v`
6. `type_system/subtyping.v`
7. `type_system/declarational.v`
8. `type_system/wf_lemmas.v`
9. `type_system/subtyping_lemmas.v`
10. `logic/logic_aux_lemmas.v`
11. `type_system/type_aux_lemmas.v`
12. `type_system/instantiation_lemmas.v`
13. `type_system/type_lemmas.v`
14. `logic/logic_tactics.v`
15. `logic/logic_lemmas.v`

Locations of important proofs:
- **Substitution lemmas** are located in `type_system/type_aux_lemmas.v` for single variable substitution and `type_system/instantiation_lemmas.v` for parallel substitution. The additional substitution lemmas for the logic are in `logic/logic_lemmas.v`
- **Logic properties** such as admissibility of subtyping are located in `logic/logic_aux_lemmas.v`.
- **Safety** is located in `type_system/type_lemmas.v`.
- **Examples** are in the folder `examples`. This branch features the examples for mutable state. Other examples are on the branch `master`.