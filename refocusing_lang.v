Require Export Util.
Require Import Program.


Module Type RED_LANG.

  (** The languages of terms, values, redex, and context, the empty context is also needed. *)
  Parameters term ckind elem_context : Set. 
  Parameters value redex : ckind -> Set.
  Parameter  ckind_trans : ckind -> elem_context -> ckind.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).
  Parameter  init_ckind : ckind.
  Parameter  dead_ckind : ckind -> Prop.
(*  Definition ckind_L := { k : ckind | ~ dead_ckind k }.
  Coercion ckind_L2any (kL : ckind_L) := proj1_sig kL.*)

  Axiom ckind_death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec). 

  Inductive context : ckind -> ckind -> Set :=
  | empty : forall {k}, context k k
  | ccons : forall (ec : elem_context) {k1 k2}, context k1 k2 -> context k1 (k2+>ec).
  Notation "[_]" := empty.
  Infix "=:" := ccons (at level 60, right associativity).

  (** The values and redexes are sublanguages of terms *)
  Parameter value_to_term : forall {k}, value k -> term.
  Parameter redex_to_term : forall {k}, redex k -> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Coercion value_to_term : value >-> term.
  Coercion redex_to_term : redex >-> term.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context k1' k2' return context k3 k1' -> context k3 k2' with
      | [_]     => fun c1' => c1'
      | ec=:c0' => fun c1' => ec =: compose c0' c1'
      end c1.
  Infix "~+" := compose (at level 60, right associativity).

  Parameter atom_plug : term -> elem_context -> term.

  Axiom atom_plug_injective1 : forall t0 t1 ec,
      atom_plug t0 ec = atom_plug t1 ec -> t0 = t1.

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [_]    => t 
      | ec=:c' => plug (atom_plug t ec) c'
      end.

  Definition transitable_from k ec := ~ dead_ckind (k+>ec).
  Definition ec_siblings ec0 ec1 := exists t0 t1, atom_plug t0 ec0 = atom_plug t1 ec1.


  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Parameter contract : forall {k}, redex k -> option term.

  Definition only_empty t k := 
      forall t' {k'} (c : context k k'), ~ dead_ckind k' -> plug t' c = t -> 
          k = k' /\ c ~= @empty k.

  Definition only_trivial (t : term) (k : ckind) : Prop := 
      forall t' {k'} (c : context k k'), plug t' c = t -> 
          k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = value_to_term v.

  Axiom value_trivial : forall k (v : value k), only_trivial (value_to_term v) k.
  Axiom redex_trivial : forall k (r : redex k), only_trivial (redex_to_term r) k.
  Axiom value_redex   : forall k (v : value k) (r : redex k), 
                            value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : 
      forall k (t : term), only_trivial t k ->
         (exists (v : value k), t = value_to_term v) \/
         (exists (r : redex k), t = redex_to_term r).

  (** Datatype of decompositions -- either a value or a redex in a context 
      (analogous to the decompose lemma) *)
  Inductive decomp k : Set :=
  | d_val : value k -> decomp k
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k.

  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Inductive interm_dec k : Set :=
  | in_red  : redex k  -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_dead : interm_dec k.

  Arguments in_red {k} _. Arguments in_val {k} _. Arguments in_term {k} _ _.

  Definition decomp_to_term {k} (d : decomp k) : term :=
      match d with
      | d_val v      => value_to_term v
      | d_red _ r c0 => plug r c0
      end.
  Coercion decomp_to_term : decomp >-> term.

  Axiom proper_death : forall k1, dead_ckind k1 -> 
                           ~ exists k2 (c : context k1 k2) (r : redex k2), True.

End RED_LANG.




Module Type RED_REF_LANG.

  Declare Module R : RED_LANG.

  Import R.

  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.

  Axiom dec_term_liveness : 
      forall t k t0 ec0, dec_term t k = in_term t0 ec0 ->
      ~ dead_ckind (k+>ec0).

  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec, t = atom_plug t0 ec -> subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.

  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.

  Parameter ec_order : ckind -> elem_context -> elem_context -> Prop.
  Notation "k |~  a << b " := (ec_order k a b) (at level 40, no associativity).
  Axiom wf_eco : forall k, well_founded (ec_order k).


  (*Definition ec_proper_sub ec t k := 

      exists t0 ec0, dec_term t k = R.in_term t0 ec0 /\ (ec0 = ec \/ k |~ ec << ec0).


  Definition indecomp_proper {k1 k2} (c : R.context k1 k2) t :=

      forall ec {k} (c0 : R.context _ k2) (c1 : R.context k1 k), 
          c0~+ec=:c1 = c -> ec_proper_sub ec (R.plug t (c0~+ec=:[_])) k.*)


  Axiom dec_term_red_empty  : forall t k r, 
                                  dec_term t k = in_red r -> only_empty t k.
  Axiom dec_term_val_empty  : forall t k v, 
                                  dec_term t k = in_val v -> only_empty t k.
  Axiom dec_term_term_top   : forall t t' k ec, 
            dec_term t k = in_term t' ec -> forall ec', ~ k |~ ec << ec'.
  Axiom dec_context_red_bot : 
      forall k ec v r, dec_context ec k v = in_red r -> 
          forall ec' t', atom_plug t' ec' = atom_plug (value_to_term v) ec -> 
              ~ k |~ ec' << ec.
  Axiom dec_context_val_bot : forall k ec v v', 
            dec_context ec k v = R.in_val v' -> forall ec', ~ k |~ ec' << ec.
  Axiom dec_context_term_next : 
      forall ec k v t ec', dec_context ec k v = in_term t ec' -> 
      k |~ ec' << ec /\ forall ec'', k |~ ec'' << ec -> ~ k |~ ec' << ec''.
  Axiom dec_term_ec_most_transitable : forall {t0 ec0 t1 ec1 k},
      transitable_from k ec1 ->
      dec_term (atom_plug t1 ec1) k = in_term t0 ec0 ->
      transitable_from k ec0.

  Axiom dec_term_correct : forall t k, match dec_term t k with
      | in_red r => redex_to_term r = t
      | in_val v => value_to_term v = t
      | in_term t' ec => atom_plug t' ec = t
      | in_dead => dead_ckind k 
      end.
  Axiom dec_context_correct : forall ec k v, match dec_context ec k v with
      | in_red r => redex_to_term r = R.atom_plug (R.value_to_term v) ec
      | in_val v' => value_to_term v' = R.atom_plug (R.value_to_term v) ec
      | in_term t ec' => atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
      | in_dead => dead_ckind (R.ckind_trans k ec) 
      end.
  Axiom dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead k.
  Axiom dec_context_from_dead : 
      forall ec k v, dead_ckind (ckind_trans k ec) -> dec_context ec k v = in_dead k.


  Axiom ec_order_antisym : forall k ec ec0, 
      k |~ ec << ec0 -> ~ k |~ ec0 << ec.
  Axiom ec_order_trans : forall k ec0 ec1 ec2,
      k |~ ec0 << ec1 -> k |~ ec1 << ec2 -> k |~ ec0 << ec2.
  Axiom ec_order_comp_if :
      forall ec0 ec1, ec_siblings ec0 ec1 -> 
      forall k, transitable_from k ec0 -> transitable_from k ec1 ->
      k |~ ec0 << ec1 \/ k |~ ec1 << ec0 \/ ec0 = ec1.
  Axiom ec_order_comp_fi :
      forall ec0 ec1 k, k |~ ec0 << ec1 ->
      ec_siblings ec0 ec1 /\ transitable_from k ec0 /\ transitable_from k ec1.

  Axiom elem_context_det : forall t0 t1 k ec0 ec1,
      k |~ ec0 << ec1 -> atom_plug t0 ec0 = atom_plug t1 ec1 ->
      exists v : R.value (k+>ec1), t1 = value_to_term v.

End RED_REF_LANG.

(*
Module RED_REF_LANG_Facts (R : RED_REF_LANG) (RP : LANG_PROP R.R).

  Import R.R.

  Lemma indecomp_proper_ec :
      forall {k1 k2} (c : context k1 k2) ec t, 
          R.indecomp_proper (ec=:c) t -> R.indecomp_proper c (atom_plug t ec).

  Proof with eauto.
  unfold R.indecomp_proper.
  intros.
  cut (R.ec_proper_sub ec0 (plug t (((ec=:[_]) ~+ c0) ~+ ec0 =: [_])) k).
  eauto.

  apply H with (c1:=c1); simpl.
  apply f_equal...
  Qed.

End RED_REF_LANG_Facts.
*)

  Ltac prove_st_wf := 
      intro a; constructor; induction a; 
      (
          intros y H; 
          inversion H as [t t0 ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).
  Ltac prove_ec_wf := 
      intros k a; destruct k, a; repeat 
      (
          constructor; 
          intros ec T; 
          destruct ec; inversion T; subst; clear T
      ).


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