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

  Axiom ckind_death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).


  Inductive context : ckind -> ckind -> Set :=
  | empty : forall {k}, context k k
  | ccons : forall (ec : elem_context) {k1 k2}, context k1 k2 -> context k1 (k2+>ec).
  Notation "[_]" := empty.
  Infix "=:" := ccons (at level 60, right associativity).

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context k1' k2' return context k3 k1' -> context k3 k2' with
      | [_]     => fun c1' => c1'
      | ec=:c0' => fun c1' => ec =: compose c0' c1'
      end c1.
  Infix "~+" := compose (at level 60, right associativity).


  Axiom proper_death : forall k1, dead_ckind k1 -> 
                           ~ exists k2 (c : context k1 k2) (r : redex k2), True.


  (** The values and redexes are sublanguages of terms *)
  Parameter value_to_term : forall {k}, value k -> term.
  Coercion  value_to_term : value >-> term.
  Parameter redex_to_term : forall {k}, redex k -> term.
  Coercion  redex_to_term : redex >-> term.

  Axiom value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.


  Parameter atom_plug : term -> elem_context -> term.
  Notation "ec :[ t ]" := (atom_plug t ec) (at level 0, t at level 99).

  Axiom atom_plug_injective1 : forall ec {t0 t1},
      ec:[t0] = ec:[t1] -> t0 = t1.

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [_]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0, t at level 99).

  Definition strict_ec ec t := exists t', ec:[t'] = t.


  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Parameter contract : forall {k}, redex k -> option term.


(*  Definition transitable_from k ec := ~ dead_ckind (k+>ec).
  Definition ec_siblings ec0 ec1 := 
      exists t0 t1, atom_plug t0 ec0 = atom_plug t1 ec1.*)

  Definition only_empty t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= @empty k.

  Definition only_trivial t k :=
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = v.


  Axiom value_trivial : forall {k} (v : value k), only_trivial v k.
  Axiom redex_trivial : forall {k} (r : redex k), only_trivial r k.
  Axiom value_redex   : forall {k} (v : value k) (r : redex k), 
                            value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : 
      forall k t, only_trivial t k ->
         (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).


  (** Datatype of decompositions -- either a value or a redex in a context 
      (analogous to the decompose lemma) *)
  Inductive decomp k : Set :=
  | d_val : value k -> decomp k
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k.

  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v      => value_to_term v
      | d_red _ r c0 => c0[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_dead : interm_dec k.

  Arguments in_red {k} _. Arguments in_val {k} _. Arguments in_term {k} _ _.

End RED_LANG.



Module Type RED_REF_LANG.

  Declare Module R : RED_LANG.
  Import R.

  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.


  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
      | in_dead       => dead_ckind k 
      end.

  Axiom dec_term_from_dead : 
      forall t k, dead_ckind k -> dec_term t k = in_dead k.

  Axiom dec_term_next_alive : 
      forall t k {t0 ec0}, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).


  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.

  Axiom dec_context_from_dead : 
      forall ec k (v : value (k+>ec)), 
          dead_ckind (k+>ec) -> dec_context ec k v = in_dead k.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall {t t0} ec, t = ec:[t0] -> subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Parameter ec_order : ckind -> term -> elem_context -> elem_context -> Prop.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).
  Axiom wf_eco : forall k t, well_founded (ec_order k t).

  Axiom ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Axiom ec_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.

  Axiom ec_order_comp_if : forall t ec0 ec1,
      strict_ec ec0 t -> strict_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.

  Axiom ec_order_comp_fi : forall k t ec0 ec1,
      k, t |~ ec0 << ec1  ->  strict_ec ec0 t /\ strict_ec ec1 t /\ 
                                  ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).


  Axiom dec_term_red_empty : forall t k {r}, dec_term t k = in_red r -> only_empty t k.
  Axiom dec_term_val_empty : forall t k {v}, dec_term t k = in_val v -> only_empty t k.

  Axiom dec_term_term_top : 
      forall t k {t' ec}, dec_term t k = in_term t' ec -> 
          forall ec',  ~ k, t |~ ec << ec'.

  Axiom dec_context_red_bot : 
      forall k ec v {r}, dec_context ec k v = in_red r -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_val_bot : 
      forall k ec v {v'}, dec_context ec k v = in_val v' -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.

  Axiom dec_context_term_next : 
      forall ec0 k v {t ec1}, dec_context ec0 k v = in_term t ec1 -> 
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.


  Axiom elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

End RED_REF_LANG.


  Ltac prove_st_wf := 
      intro t; constructor; induction t; 
      (
          intros ? H; 
          inversion H as [? ? ec DECT]; subst; 
          destruct ec; inversion DECT; subst; 
          constructor; auto
      ).

  Ltac prove_ec_wf := 
      intros k t ec; destruct k, t, ec; repeat 
      (
          constructor; 
          intros ec H; 
          destruct ec; inversion H; dep_subst; clear H
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