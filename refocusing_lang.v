Require Export List.
Require Import Program.
Require Export Util.
Require Import Eqdep.

Module Type RED_LANG.

  (** The languages of terms, values, redex, and context, the empty context is also needed. *)
  Parameters term ckind elem_context : Set. 
  Parameters value redex : ckind -> Set.
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Parameter  init_ckind : ckind.
  Inductive context : ckind -> ckind -> Set :=
  | empty : forall {k}, context k k
  | ccons : forall (ec : elem_context) {k1 k2}, context k1 k2 -> context k1 (ckind_trans k2 ec).

  (** The values and redexes are sublanguages of terms *)
  Parameter value_to_term : forall {k}, value k -> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Axiom value_to_term_injective : forall k (v v' : value k),
    value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : forall k (r r' : redex k),
    redex_to_term r = redex_to_term r' -> r = r'.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context k1' k2' return context k3 k1' -> context k3 k2' with
      | empty _ => fun c1' => c1'
      | ccons ec _ _ c0' => fun c1' => ccons ec (compose c0' c1')
      end c1.
  Parameter atom_plug : term -> elem_context -> term.
  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term := match c with
  | empty _ => t | ccons ec _ _ c' => plug (atom_plug t ec) c' end.
    

  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Parameter contract : forall {k}, redex k -> option term.

  Definition only_empty (t : term) (k : ckind) : Prop := 
    forall t' k' (c : context k k'), plug t' c = t -> k = k' /\ c ~= @empty k.
  Definition only_trivial (t : term) (k : ckind) : Prop := 
    forall t' k' (c : context k k'), plug t' c = t -> 
      k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = value_to_term v.

  Axiom value_trivial : forall k (v : value k), only_trivial (value_to_term v) k.
  Axiom redex_trivial : forall k (r : redex k), only_trivial (redex_to_term r) k.
  Axiom value_redex   : forall k (v : value k) (r : redex k), value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : forall k (t : term), only_trivial t k ->
    (exists (v : value k), t = value_to_term v) \/ (exists (r : redex k), t = redex_to_term r).

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
  Inductive decomp k : Set :=
  | d_val : value k -> decomp k
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k.

  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Inductive interm_dec k : Set :=
  | in_red  : redex k  -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k.

  Arguments in_red {k} _. Arguments in_val {k} _. Arguments in_term {k} _ _.

  Definition decomp_to_term {k} (d : decomp k) : term :=
  match d with
    | d_val v => value_to_term v
    | d_red _ r c0 => plug (redex_to_term r) c0
  end.

End RED_LANG.


Module RED_LANG_Facts (R : RED_LANG).

    Lemma ccons_inj : forall ec {k1 k2} c ec' {k2'} c', 
    R.ckind_trans k2 ec = R.ckind_trans k2' ec' ->
    @R.ccons ec k1 k2 c ~= @R.ccons ec' k1 k2' c' ->
    ec = ec' /\ k2 = k2' /\ c ~= c'.
    Proof.
    intros.
    assert (H1 := JMeq_eq_depT _ _ _ _ _ _ H H0).
    assert (H2 := eq_dep_eq_sigT _ _ _ _ _ _ H1). 
    inversion H2; subst.
    assert (H7' := inj_pair2 _ _ _ _ _ H7); subst; clear H7.
    assert (H7'' := inj_pair2 _ _ _ _ _ H7'); subst; clear H7'.
    auto.
    Qed.

End RED_LANG_Facts.


Module Type LANG_PROP (R : RED_LANG).

  Axiom plug_empty : forall t k, R.plug t (@R.empty k) = t.
  Axiom compose_empty : forall {k1 k2} (c : R.context k1 k2), c = R.compose c R.empty.
  Axiom plug_compose : forall k1 k2 k3 (c0 : R.context k1 k2) (c1 : R.context k3 k1) 
                               (t : R.term), 
                           R.plug t (R.compose c0 c1) = R.plug (R.plug t c0) c1.

End LANG_PROP.

Module Type RED_REF_LANG.

  Declare Module R : RED_LANG.

  Parameter dec_term    : R.term -> forall k,  R.interm_dec k.
  Parameter dec_context : forall (ec : R.elem_context) (k : R.ckind), 
                              R.value (R.ckind_trans k ec) -> R.interm_dec k.

  Inductive subterm_one_step : R.term -> R.term -> Prop :=
  | st_1 : forall t t0 ec, t = R.atom_plug t0 ec -> subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.

  Definition subterm_order := clos_trans_1n R.term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.

  Parameter ec_order : R.ckind -> R.elem_context -> R.elem_context -> Prop.
  Notation "k |-  a << b " := (ec_order k a b) (at level 40, no associativity).
  Axiom wf_eco : forall k, well_founded (ec_order k).

  Axiom dec_term_red_empty  : forall t k (r : R.redex k), 
                                  dec_term t k = R.in_red r -> R.only_empty t k.
  Axiom dec_term_val_empty  : forall t k (v : R.value k), 
                                  dec_term t k = R.in_val v -> R.only_empty t k.
  Axiom dec_term_term_top   : forall t t' k ec, 
            dec_term t k = R.in_term t' ec -> forall ec', ~ k |- ec << ec'.
  Axiom dec_context_red_bot : forall k ec v r, 
            dec_context ec k v = R.in_red r -> forall ec', ~ k |- ec' << ec.
  Axiom dec_context_val_bot : forall k ec v v', 
            dec_context ec k v = R.in_val v' -> forall ec', ~ k |- ec' << ec.
  Axiom dec_context_term_next : 
    forall ec k v t ec', dec_context ec k v = R.in_term t ec' -> 
        k |- ec' << ec /\ forall ec'', k |- ec'' << ec -> ~ k |- ec' << ec''.

  Axiom dec_term_correct : forall t k, match dec_term t k with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t' ec => R.atom_plug t' ec = t
    end.
  Axiom dec_context_correct : forall ec k v, match dec_context ec k v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v' => R.value_to_term v' = R.atom_plug (R.value_to_term v) ec
    | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
    end.

  Axiom ec_order_antisym : forall k (ec ec0 : R.elem_context), k |- ec << ec0 -> ~ k |- ec0 << ec.
  (*Axiom dec_ec_ord : forall t0 t1 k ec0 ec1, 
      R.atom_plug t0 ec0 = R.atom_plug t1 ec1 -> 
      k |- ec0 << ec1 \/ k |- ec1 << ec0 \/ (t0 = t1 /\ ec0 = ec1).*)
  Axiom elem_context_det : forall t0 t1 k ec0 ec1, 
    k |- ec0 << ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
    exists v : R.value (R.ckind_trans k ec1), t1 = R.value_to_term v.

End RED_REF_LANG.

  Ltac prove_st_wf := intro a; constructor; induction a; (intros y H; 
    inversion H as [t t0 ec DECT]; subst; destruct ec; inversion DECT; subst; constructor; auto).
  Ltac prove_ec_wf := intro a; destruct a; repeat (constructor; intros ec T; destruct ec; inversion T; subst; clear T).

Module Type ABSTRACT_MACHINE.

  Parameters term configuration : Set.
  Parameter value : Set.
  Parameter c_init : term -> configuration.
  Parameter c_final : value -> configuration.
  Parameter transition : configuration -> configuration -> Prop.

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.

Module Type SOS_SEM.

  Parameters term value : Set.
  Parameter step : term -> term -> Prop.
  Parameter value_to_term : value -> term.

  Inductive step_close : term -> value -> Prop :=
  | s_val  : forall v, step_close (value_to_term v) v
  | s_step : forall t t0 v, step t t0 -> step_close t0 v -> step_close t v.

End SOS_SEM.