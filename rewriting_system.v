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



Class LABELED_REWRITING_SYSTEM (label configuration : Set) :=
{
    ltransition : label -> configuration -> configuration -> Prop
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



Instance RWS_is_LRWS                                    {conf} `(REWRITING_SYSTEM conf) :
                                                    LABELED_REWRITING_SYSTEM unit conf :=
{
    ltransition := fun (_ : unit) => transition
}.




Require Import Fin2 Vector2 Program.

Open Local Scope vector.

Definition path_in                                    {conf} `(REWRITING_SYSTEM conf) {n}
    (cs : Vector.t conf n) : Prop :=

    match cs with
    | []          => False
    | cons c n cs => forall m : Fin.t n, (c::cs)[@m] → cs[@m]
    end.
Definition path {conf} {rws : REWRITING_SYSTEM conf} {n} := @path_in conf rws n.


Definition lpath_in               {label conf} `(LABELED_REWRITING_SYSTEM label conf) {n}
    (cs : Vector.t conf (S n)) (ls : Vector.t label n) : Prop :=

    match cs in Vector.t _ n return Vector.t label (pred n) -> Prop with
    | []          => fun _  => False
    | cons c n cs => fun ls => forall m : Fin.t n, ls[@m] |~ (c::cs)[@m] → cs[@m]
    end ls.
Definition lpath {label conf} {lrws : LABELED_REWRITING_SYSTEM label conf} {n} := 
    @lpath_in label conf lrws n.


Lemma path_snoc                                     {conf} `{REWRITING_SYSTEM conf} {n} :
    forall (cs : Vector.t conf (S n)) c, path cs -> (last cs) → c -> path (cs ++ [c]).

Proof.
  intros cs c H0 H1.
  dependent destruction cs.
  revert h H0 H1.
  induction cs; 
      intros c0 H0 H1 m.
  - dependent destruction m.
    + auto.
    + inversion m.
  - dependent destruction m.
    + apply (H0 Fin.F1).
    + apply IHcs.
      * intro m0; apply (H0 (Fin.FS m0)).
      * auto.
Qed.

