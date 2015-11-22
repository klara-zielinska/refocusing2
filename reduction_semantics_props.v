Require Import reduction_semantics reduction_semantics_facts.


Coercion bool2prop b := match b with true => True | false => False end.


Module Type SAFE_RED_REGION (R : RED_LANG).

  Import R.

  Parameter safe : ckind -> term -> Prop.
  Axiom progresvation : 
      forall {k1 k2} (c : context k1 k2) (r : redex k2), 
          safe k1 c[r] -> exists t, contract r = Some t /\ safe k1 c[t].
  (*Axiom safe_decomp1  : forall k t ec t', safe k t -> t = ec:[t'] -> 
                            ~dead_ckind (k+>ec) -> safe (k+>ec) t'.*)

End SAFE_RED_REGION.



(*
Module SAFE_RED_REGION_Facts (R : RED_LANG) (Reg : SAFE_RED_REGION R).

  Module RF := RED_LANG_Facts R.
  Import R Reg RF.

  Lemma safe_decomp : forall {k1 k2} (c : context k1 k2) t, ~dead_ckind k2 -> 
                          safe k1 c[t] -> safe k2 t.
  Proof.
    intros k1 k2 c.
    induction c; intros t H H0;
    solve [eauto using safe_decomp1, death_propagation2].
  Qed.

End SAFE_RED_REGION_Facts.
  *)  


(*
Module Type INIT_RED_SAFE (R : RED_LANG) (Reg : SAFE_RED_REGION R).

  Import R Reg.
  Axiom init_safe : forall t, safe init_ckind t.

End INIT_RED_SAFE.*)


(*
Module Type RED_CAL.
  Declare Module RedLang : RED_LANG.
  Declare Module RedSem  : RED_SEM RedLang.
End RED_CAL.



Module SAFE_SUB_REF (R : RED_LANG) (S : RED_SEM R) (Reg : SAFE_RED_REGION R) 
                        (*IS : INIT_RED_SAFE R Reg*) <: RED_CAL.

  Module Type CS.
    Inductive context (k1 : R.ckind) : R.ckind -> Set :=
    | empty : context k1 k1
    | ccons : forall (ec : R.elem_context) {k2}, context k1 k2 -> context k1 (R.ckind_trans k2 ec).
    Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.
    
    Inductive decomp k : Set :=
    | d_red : forall {k'}, R.redex k' -> context k k' -> decomp k
    | d_val : R.value k -> decomp k.
    Arguments d_red {k k'} _ _. Arguments d_val {k} _.
    
  End CS.

  Module CSM : CS := R.

  Module RedLang.

    Definition term := { t | exists k, Reg.safe k t }.
    Coercion org_term (t : term) := proj1_sig t.

    Definition elem_context := R.elem_context.
    Definition ckind := R.ckind.
    Definition ckind_trans := R.ckind_trans.
    Infix "+>" := ckind_trans (at level 50, left associativity).

    Include CSM.

    Notation "[.]"      := empty.
    Notation "[.]( k )" := (@empty k).
    Infix    "=:"       := ccons (at level 60, right associativity).

    Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                        {k3} (c1 : context k3 k1) : context k3 k2 := 
        match c0 in context _ k2' return context k3 k2' with
        | [.]     => c1
        | ec =: c0' => ec =: compose c0' c1
        end.
    Infix "~+" := compose (at level 60, right associativity).

    Definition elem_plug (t : term) (ec : elem_context) : term. (* := *) refine (
        exist _ (R.elem_plug t ec) _).
    Proof. destruct t as [t [k H]]. exists (k+>ec). simpl.  eapply Reg.safe_decomp; simpl; auto.
    
    Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).

    Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
        match c with
        | [.]    => t 
        | ec=:c' => plug ec:[t] c'
        end.
    Notation "c [ t ]" := (plug t c) (at level 0).

    Axiom elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.

    Definition immediate_ec ec t := exists t', ec:[t'] = t.

    Parameters value redex : ckind -> Set.

    Parameter value_to_term : forall {k}, value k -> term.
    Coercion  value_to_term : value >-> term.
    Parameter redex_to_term : forall {k}, redex k -> term.
    Coercion  redex_to_term : redex >-> term.

    Axiom value_to_term_injective : 
        forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
    Axiom redex_to_term_injective : 
        forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.



    Parameter  init_ckind : ckind.
    Parameter  dead_ckind : ckind -> Prop. 

    Axiom death_propagation : 
        forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).
    Axiom proper_death : 
        forall k, dead_ckind k -> ~ exists (r : redex k), True.


    Axiom value_trivial1 : forall {k} (v : value k) ec {t}, 
                               ~dead_ckind (k+>ec) -> ec:[t] = v -> 
                                   exists (v' : value (k+>ec)), t = v'.
    Axiom value_redex    : forall {k} (v : value k) (r : redex k), 
                               value_to_term v <> redex_to_term r.

    Axiom decompose : forall (t : term) k1, ~ dead_ckind k1 ->
        (exists (v : value k1), t = v) \/
        (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).


    Parameter contract : forall {k}, redex k -> option term.
*)




Module Type RED_PROGRESS (R : RED_LANG).

  Import R.
  Axiom progress : forall {k} (r : redex k), exists t, contract r = Some t.

End RED_PROGRESS.