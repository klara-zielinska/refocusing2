Require Import Relations.



Class REWRITING_SYSTEM (configuration : Set) :=
{
    transition : configuration -> configuration -> Prop
}.


Notation "`( rw ) c1 → c2"  := (@transition _ rw c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "`( rw ) c1 →+ c2" := (clos_trans_1n _ (@transition _ rw) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "`( rw ) c1 →* c2" := (clos_refl_trans_1n _ (@transition _ rw) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).

Notation "c1 → c2"  := (transition c1 c2)                (no associativity, at level 70).
Notation "c1 →+ c2" := (clos_trans_1n _ transition c1 c2)
                                                         (no associativity, at level 70).
Notation "c1 →* c2" := (clos_refl_trans_1n _ transition c1 c2)
                                                         (no associativity, at level 70).



Class LABELED_REWRITING_SYSTEM (label lconfiguration : Set) :=
{
    ltransition : label -> lconfiguration -> lconfiguration -> Prop
}.


Notation "`( rw ) l |~ c1 → c2"  := (@ltransition _ _ rw l c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).
Notation "`( rw ) l |~ c1 →+ c2" := (clos_trans_1n _ (@ltransition _ _ rw l) c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).
Notation "`( rw ) l |~ c1 →* c2" := (clos_refl_trans_1n _ (@ltransition _ _ rw l) c1 c2)
                                      (no associativity, at level 70, c1, l at level 69).

Notation "l |~ c1 → c2"  := (ltransition l c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "l |~ c1 →+ c2" := (clos_trans_1n _ (ltransition l) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).
Notation "l |~ c1 →* c2" := (clos_refl_trans_1n _ (ltransition l) c1 c2)
                                         (no associativity, at level 70, c1 at level 69).



Instance LRWS_is_RWS {conf} `(REWRITING_SYSTEM conf) : LABELED_REWRITING_SYSTEM unit conf:=
{
    ltransition := fun (_ : unit) => transition
}.
