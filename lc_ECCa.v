Require Import refocusing_substitutions.
Require Import Program.
(*Require Import Setoid.*)

Module lc_ECCa <: RED_LANG.

Definition v_name := nat.

Inductive expr :=
| App : expr -> expr -> expr
| Var : v_name -> expr
| Lam : v_name -> expr -> expr.
Definition term := expr.

Inductive _ckind := C | ECa | CBot.
Definition ckind := _ckind.

Inductive val : ckind -> Type :=

| vCLam : v_name -> val C -> val C
| vCVar : v_name -> val C
| vCApp : valCa -> val C -> val C

| vECaLam : v_name -> term -> val ECa
| vECaVar : v_name -> val ECa
| vECaApp : valCa -> val C -> val ECa

| vCBot : term -> val CBot

with valCa :=
| vCaVar : v_name -> valCa
| vCaApp : valCa -> val C -> valCa.

Definition value := val.

Inductive red : ckind -> Set :=
| rCApp   : v_name -> term -> term -> red C
| rECaApp : v_name -> term -> term -> red ECa.
Definition redex := red.

Inductive ec :=
| lam_c : v_name -> ec
| ap_r  : term -> ec
| ap_l  : valCa -> ec.
Definition elem_context := ec.

Definition ckind_trans (k : ckind) (ec : elem_context) := 
match k with
| C    => match ec with lam_c _ => C    | ap_r _ => ECa | ap_l _ => C end
| ECa  => match ec with lam_c _ => CBot | ap_r _ => ECa | ap_l _ => C end
| _    => CBot
end.
Definition init_ckind : ckind := C.
Definition dead_ckind (k : ckind) := match k with CBot => True | _ => False end.

Lemma ckind_death_propagation : 
    forall k, dead_ckind k -> forall ec, dead_ckind (ckind_trans k ec).
Proof.
intuition.
destruct k;
inversion H;
reflexivity.
Qed.


Inductive context : ckind -> ckind -> Set :=
| empty : forall {k}, context k k
| ccons : forall (ec : elem_context) {k1 k2}, context k1 k2 -> context k1 (ckind_trans k2 ec).
Notation "[_]" := empty.
Infix "=:" := ccons (at level 60, right associativity).


Fixpoint value_to_term {k} (v : value k) : term :=
match v with
| vCLam x v => Lam x (value_to_term v)
| vCVar x => Var x
| vCApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
| vECaLam x t => Lam x t
| vECaVar x => Var x
| vECaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
| vCBot t => t
end
with valCa_to_term v : term :=
match v with
| vCaVar x => Var x
| vCaApp v1 v2 => App (valCa_to_term v1) (value_to_term v2)
end.
Coercion value_to_term : value >-> term.
Coercion valCa_to_term : valCa >-> term.


Definition redex_to_term {k} (r : redex k) : term :=
match r with
| rCApp x t1 t2 => App (Lam x t1) t2
| rECaApp x t1 t2 => App (Lam x t1) t2
end.
Coercion redex_to_term : redex >-> term.


Scheme val_Ind := Induction for val Sort Prop
  with valCa_Ind := Induction for valCa Sort Prop.


Lemma value_to_term_injective : 
    forall k (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

Proof with auto.
induction v using val_Ind with 
(P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
(P0 := fun v   => forall v' : valCa, valCa_to_term v = valCa_to_term v' -> v = v');
dependent destruction v'; intro H; inversion H; f_equal...
Qed.
Hint Resolve value_to_term_injective : lc_ecca.

Lemma valCa_to_term_injective : 
    forall v v', valCa_to_term v = valCa_to_term v' -> v = v'.

Proof with auto.
induction v using valCa_Ind with 
(P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
(P0 := fun v   => forall v' : valCa, valCa_to_term v = valCa_to_term v' -> v = v');
dependent destruction v'; intro H; inversion H; f_equal...
Qed.
Hint Resolve value_to_term_injective : lc_ecca.


Lemma redex_to_term_injective : 
    forall k (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

Proof with auto with lc_ecca.
destruct k;
induction r; dependent destruction r'; simpl; intro H; inversion H; f_equal...
Qed.
Hint Resolve redex_to_term : lc_ecca.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Fixpoint compose {k1 k2} (c0 : context k1 k2) {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context k1' k2' return context k3 k1' -> context k3 k2' with
      | [_]     => fun c1' => c1'
      | ec=:c0' => fun c1' => ec =: compose c0' c1'
      end c1.
  Infix "~+" := compose (at level 60, right associativity).

  Definition atom_plug (t : term) (ec : elem_context) : term :=
  match ec with
  | lam_c x => Lam x t
  | ap_r tr => App t tr
  | ap_l v  => App (v : term) t
  end.

  Lemma atom_plug_injective1 : forall t0 t1 ec,
      atom_plug t0 ec = atom_plug t1 ec -> t0 = t1.
  Proof.
  intros.
  destruct ec0; injection H; trivial.
  Qed.

  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [_]    => t 
      | ec=:c' => plug (atom_plug t ec) c'
      end.

  Definition transitable_from k ec := ~ dead_ckind (ckind_trans k ec).
  Definition ec_siblings ec0 ec1 := exists t0 t1, atom_plug t0 ec0 = atom_plug t1 ec1.

  Parameter subst : v_name -> expr -> expr -> expr.

  (*Import Arith.Peano_dec.
  Fixpoint subst x ex e :=
  match e with
  | Z  => Z
  | S e1 => S (subst x ex e1)
  | App e1 e2 => App (subst x ex e1) (subst x ex e2) 
  | Var y => if eq_nat_dec y x then ex else Var y
  | Lam y e1 => if eq_nat_dec y x then Lam y e1 else Lam y (subst x ex e1)
  | Case e0 e1 y e2 => Case (subst x ex e0) (subst x ex e1) y 
                          (if eq_nat_dec y x then e2 else (subst x ex e2)) 
  | Letv y e1 e2 => Letv y (subst x ex e1) (if eq_nat_dec y x then e2 else subst x ex e2)
  | Fix y e1 => if eq_nat_dec y x then Fix y e1 else Fix y (subst x ex e1)
  | Pair e1 e2 => Pair (subst x ex e1) (subst x ex e2)
  | Fst e1 => Fst (subst x ex e1)
  | Snd e1 => Snd (subst x ex e1)
  end.*)

  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Definition contract {k} (r : redex k) : option term :=
  match r with
  | rCApp   x t tx => Some (subst x tx t)
  | rECaApp x t tx => Some (subst x tx t)
  end.

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
  Inductive decomp (k : ckind) : Type :=
       d_val : value k -> decomp k
     | d_red : forall k' : ckind, redex k' -> context k k' -> decomp k.

  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Inductive interm_dec k : Type :=
  | in_red  : redex k  -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_dead : interm_dec k.

  Arguments in_red {k} _. Arguments in_val {k} _. Arguments in_term {k} _ _.

  Definition decomp_to_term {k} (d : decomp k) : term :=
  match d with
    | d_val v => value_to_term v
    | d_red _ r c0 => plug (redex_to_term r) c0
  end.

  Definition only_empty (t : term) (k : ckind) : Prop := 
      forall t' k' (c : context k k'), plug t' c = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= @empty k.

  Definition only_trivial (t : term) (k : ckind) : Prop := 
      forall t' k' (c : context k k'),  plug t' c = t -> 
          k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = value_to_term v.


Lemma L : forall v1 : valCa, exists v2 : value ECa, (v1 : term) = (v2 : term).
Proof with auto.
dependent destruction v1; intros.
- exists (vECaVar v)...
- exists (vECaApp v1 v)...
Qed.

Lemma LL : forall v1 : valCa, exists v2 : value C, (v1 : term) = (v2 : term).
Proof with auto.
dependent destruction v1; intros.
- exists (vCVar v)...
- exists (vCApp v1 v)...
Qed.

  Lemma value_trivial : forall k (v : value k), only_trivial (value_to_term v) k.
  Proof with auto.
    intros k1 v t k2 c; revert t.
    induction c.
    - intuition.
    - intros.
      right.
      destruct IHc with v (atom_plug t ec0) as [(H1, H2) | (v0, H1)];
          try solve [intro; apply H; apply ckind_death_propagation; auto | auto];
          subst; [ dependent destruction H2 | ]; simpl in *;
      match goal with 
      | [Hv : atom_plug ?t ?a = _ ?v |- _] => 
            destruct a; destruct v; 
            dependent_destruction2 Hv
      end;
      try solve [eexists; eauto | apply L | eexists (vCBot _); simpl; eauto ].
  Qed.

  Lemma redex_trivial : forall k (r : redex k), only_trivial (redex_to_term r) k.
  Proof with auto.
    intros k1 r t k2 c; revert t.
    induction c.
    - intuition.
    - intros.
      right.
      destruct IHc with r (atom_plug t ec0) as [(H1, H2) | (v0, H1)];
          try solve [intro; apply H; apply ckind_death_propagation; auto | auto];
          subst; [ dependent destruction H2 | ]; simpl in *;
      match goal with
      | [Hvr : atom_plug ?t ?a = _ ?r |- _] => 
            destruct a; destruct r; 
            dependent_destruction2 Hvr
      end; simpl in *; 
      try solve [ exists (vECaLam v t1); auto 
                | dependent destruction v; discriminate
                | eexists; eauto
                | apply L
                | eexists (vCBot _); simpl; eauto ].
  Qed.

  Lemma value_redex : forall k (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    destruct v; dependent destruction r; 
    try dependent destruction v0; try dependent destruction v; 
    intro H; discriminate H. 
  Qed.

  Lemma ot_subt : 
      forall t t0 ec k, (*~ dead_ckind (ckind_trans k ec) ->*)
                        only_trivial t k -> atom_plug t0 ec = t -> 
          exists v : value (ckind_trans k ec), t0 = value_to_term v.

  Proof with auto.
    intros.
    destruct (H t0 _ (ec0 =: [_])) as [(H2, H3) | (v, H2)]...
    - discriminateJM H3.
    - exists v; destruct k...
  Qed.

  Ltac ot_v t ec :=
  match goal with [Hot : (only_trivial ?H1) _ |- _] => 
      destruct (ot_subt _ t ec _ Hot) as (?v, HV); [auto | subst t]
  end.

  Ltac mlr rv :=
  match goal with
  | [ |- (exists v : value ?k, ?H1 = value_to_term v) 
         \/ (exists r : redex ?k, ?H1 = redex_to_term r)] =>
    destruct k;
    match type of rv with
    | value ?k1 => destruct k1; left; exists rv
    | redex ?k1 => destruct k1; right; exists rv
    end; simpl; auto
  end.


  Lemma plug_compose : forall k1 k2 k3 (c : context k1 k2) (c' : context k3 k1) 
                               (t : term), 
                           plug t (compose c c') = plug (plug t c) c'.
  Proof.
    intros ? ? ?; induction c; intros.
    - auto.
    - apply IHc.
  Qed.

Lemma L2 : forall t ec k, (*~ dead_ckind (ckind_trans k ec) ->*)
               only_trivial (atom_plug t ec) k -> only_trivial t (ckind_trans k ec).
Proof with eauto.
intros.
intros t' k' c H1.
destruct (H t' k' (c ~+ ec0 =: [_])) as [(H3, H4) | ?]... rewrite plug_compose... subst...
absurd_hyp H4... revert H3; clear; intro. dependent induction c; intro H; discriminateJM H.
Qed.


  Lemma trivial_val_red : 
      forall k (t : term), only_trivial t k ->
         (exists (v : value k), t = value_to_term v) \/
         (exists (r : redex k), t = redex_to_term r).

  Proof with auto.
    intros. revert k H.
    induction t; intros;
    destruct k; try solve [contradiction H; simpl; auto].
    Focus 7. 
    destruct (ot_subt _ t (lam_c v) C H); eauto; subst;
    left; exists (vCLam v x); subst...
    Focus 7.
    left; exists (vECaLam v t)...

    Focus 4.
    left; exists (vCVar v)...
    Focus 4.
    left; exists (vECaVar v)...

    Focus 1.
    destruct (ot_subt _ t1 (ap_r t2) C H); eauto; subst.
    dependent destruction x.
    right. exists (rCApp v t t2)...
    destruct (ot_subt _ t2 (ap_l (vCaVar v)) C H); eauto; subst.
    left. exists (vCApp (vCaVar v) x0)...
    destruct (ot_subt _ t2 (ap_l (vCaApp v x1)) C H); eauto; subst.
    left. exists (vCApp (vCaApp v x1) x0)...
    Focus 1.
    destruct (ot_subt _ t1 (ap_r t2) ECa H); eauto; subst.
    dependent destruction x.
    right. exists (rECaApp v t t2)...
    destruct (ot_subt _ t2 (ap_l (vCaVar v)) ECa H); eauto; subst.
    left. exists (vECaApp (vCaVar v) x0)...
    destruct (ot_subt _ t2 (ap_l (vCaApp v x1)) ECa H); eauto; subst.
    left. exists (vECaApp (vCaApp v x1) x0)...

    left; exists (vCBot (App t1 t2))...
    left; exists (vCBot (Var v))...
    left; exists (vCBot (Lam v t))...
  Qed.

  Lemma proper_death : forall k, dead_ckind k -> 
                           ~ exists k' (c : context k k') (r : redex k'), True.
  Proof.
  destruct k;
  intuition;
  destruct H0 as (k', (c, (r, _))).
  cut (k' = CBot).
  - intro H0; subst; dependent destruction r.
  - clear r; dependent induction c; auto.
    rewrite IHc; simpl; constructor.
  Qed. Print RED_LANG.

End lc_ECCa.


Module lc_ECCa_Ref <: RED_REF_LANG.

  Module R := lc_ECCa.
  Include Lang_Prop R.

  Definition dec_term t k : R.interm_dec k :=
  match k as k0 return R.interm_dec k0 with 
  | R.C => match t with
           | R.App t1 t2 => R.in_term t1 (R.ap_r t2)
           | R.Var x     => R.in_val (R.vCVar x)
           | R.Lam x t1  => R.in_term t1 (R.lam_c x)
           end
  | R.ECa => match t with
             | R.App t1 t2 => R.in_term t1 (R.ap_r t2)
             | R.Var x     => R.in_val (R.vECaVar x)
             | R.Lam x t1  => R.in_val (R.vECaLam x t1)
             end
  | R.CBot => R.in_dead R.CBot
  end.

  Definition dec_context ec k (v : R.value (R.ckind_trans k ec)) : R.interm_dec k :=
  match ec as ec0 return R.value (R.ckind_trans k ec0) -> R.interm_dec k with
  | R.lam_c x  => match k as k0 return R.value (R.ckind_trans k0 (R.lam_c x)) -> R.interm_dec k0 with
                  | R.C    => fun v => R.in_val (R.vCLam x v)
                  | R.ECa  => fun v => R.in_dead R.ECa (*val (R.vCBot (R.Lam x (R.value_to_term v)))*)
                  | R.CBot => fun v => R.in_dead R.CBot
                  end
  | R.ap_r t   => match k as k0 return R.value (R.ckind_trans k0 (R.ap_r t)) -> R.interm_dec k0 with
                  | R.CBot => fun v => R.in_dead R.CBot
                  | R.C    => fun v => match v with
                              | R.vECaLam x t0  => R.in_red (R.rCApp x t0 t)
                              | R.vECaVar x     => R.in_term t (R.ap_l (R.vCaVar x))
                              | R.vECaApp v1 v2 => R.in_term t (R.ap_l (R.vCaApp v1 v2))
                              | _ => R.in_dead R.C
                              end
                  | R.ECa  => fun v => match v with
                              | R.vECaLam x t0  => R.in_red (R.rECaApp x t0 t)
                              | R.vECaVar x     => R.in_term t (R.ap_l (R.vCaVar x))
                              | R.vECaApp v1 v2 => R.in_term t (R.ap_l (R.vCaApp v1 v2))
                              | _ => R.in_dead R.ECa
                              end
                  end
  | R.ap_l v0  => match k as k0 return R.value (R.ckind_trans k0 (R.ap_l v0)) -> R.interm_dec k0 with
                  | R.CBot => fun v => R.in_dead R.CBot
                  | R.C    => fun v => R.in_val (R.vCApp v0 v)
                  | R.ECa  => fun v => R.in_val (R.vECaApp v0 v)
                  end
  end
  v.

  Inductive subterm_one_step : R.term -> R.term -> Prop :=
  | st_1 : forall t t0 ec, t = R.atom_plug t0 ec -> subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_1n R.term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.

  Definition ec_order (k : R.ckind) (ec ec0 : R.elem_context) : Prop :=
  match k with
  | R.CBot => False
  | _      => match ec, ec0 with 
              | R.ap_l _, R.ap_r _ => True
              | _, _               => False
              end
  end.
  Notation "k |~  a << b " := (ec_order k a b) (at level 40, no associativity).
  Lemma wf_eco : forall k, well_founded (ec_order k).
  Proof.
    prove_ec_wf.
  Qed.

  Include RED_LANG_Facts R.


  Lemma dec_term_red_empty : forall t k (r : R.redex k), 
                                 dec_term t k = R.in_red r -> R.only_empty t k.
  Proof with auto.
    intros t k r H.
    destruct t; inversion H; subst; clear H;
    (
        intros t0 k' c H0; generalize dependent t0;

        induction c;
            intros; simpl in *;
        [ intuition
        | destruct (IHc _ H1 _ H0 (context_tail_liveness _ _ H)) as (H2, H3);
              subst; dependent destruction H3;
          destruct k2, ec; inversion H1 ]
    ).
  Qed.

  Lemma dec_term_from_dead : forall t k, R.dead_ckind k -> dec_term t k = R.in_dead k.
  Proof.
  intros.
  destruct k; simpl; intuition.
  Qed.

  Lemma dec_term_val_empty : forall t k (v : R.value k), 
                                 dec_term t k = R.in_val v -> R.only_empty t k.
  Proof with auto.
    intros t k v H.
    destruct t; inversion H; subst; clear H;
    intros t0 k' c H0; generalize dependent t0.
    (
        induction c;
            intros; simpl in *;
        [ intuition
        | destruct (IHc _ H1 _ H0 (context_tail_liveness _ _ H)) as (H2, H3);
              subst; dependent destruction H3;
          destruct k2, ec; inversion H1 ]
    ). 

    
        induction c;
            intros; simpl in *. intuition. destruct (IHc _ H1 _ H0 (context_tail_liveness _ _ H)) as (H2, H3);
              subst; dependent destruction H3. destruct k2, ec; inversion H0.

destruct k; intros. Focus 2.
dependent destruction c.
intuition.
destruct (context_snoc ec c) as (ec1, (c1, H2)).
rewrite H2 in H0. clear H2.
rewrite plug_compose in H0.
destruct ec1.
contradict H; apply (dead_contex_dead c1); simpl...
discriminate H0.
discriminate H0.

Focus 2.
contradict H; apply (dead_contex_dead c); simpl...

Focus 1.
discriminate.
  Qed.


  Lemma dec_term_term_top : forall t t' k ec, 
            dec_term t k = R.in_term t' ec -> forall ec', ~ k |~ ec << ec'.
  Proof.
    intros t t' k ec H ec' H0; destruct k, t; inversion H; subst; destruct ec'; inversion H0.
  Qed.


  Lemma dec_term_correct : forall t k, match dec_term t k with
      | R.in_red r => R.redex_to_term r = t
      | R.in_val v => R.value_to_term v = t
      | R.in_term t' ec => R.atom_plug t' ec = t
      | R.in_dead => R.dead_ckind k 
      end.
  Proof.
    destruct k, t; simpl; auto.
  Qed.


  Lemma dec_context_correct : forall ec k v, match dec_context ec k v with
      | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
      | R.in_val v' => R.value_to_term v' = R.atom_plug (R.value_to_term v) ec
      | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
      | R.in_dead => R.dead_ckind (R.ckind_trans k ec)
      end.
  Proof.
    destruct k, ec; dependent destruction v; simpl; auto.
  Qed.


  Lemma dec_context_from_dead : 
      forall ec k v, R.dead_ckind (R.ckind_trans k ec) -> dec_context ec k v = R.in_dead k.
  Proof.
  intros.
  destruct ec, k; simpl in *; intuition.
  Qed.
(*
  Lemma ec_siblings_uni_strong : 
     forall ec1 ec2, R.ec_siblings ec1 ec2 -> 
         forall t1, exists t2, R.atom_plug t1 ec1 = R.atom_plug t2 ec2.
  Proof with eauto.
  intros.
  destruct ec1, ec2;
  destruct H as (s1, (s2, H));
  try discriminate;
  inversion H; subst;
  try solve [exists t1; trivial]. simpl in *.
  exists s2; simpl...*)

  Lemma ec_order_comp_fi :
      forall ec0 ec1 k, k |~ ec0 << ec1 ->
      R.ec_siblings ec0 ec1 /\ R.transitable_from k ec0 /\ R.transitable_from k ec1.
  Proof with auto.
    intros.
    destruct k, ec0, ec1; 
    intuition;
    try solve [compute; auto];
        solve [exists t (R.valCa_to_term v); auto].
  Qed.


  Lemma elem_context_det : forall t0 t1 k ec0 ec1,
      k |~ ec0 << ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
      exists v : R.value (R.ckind_trans k ec1), t1 = R.value_to_term v.
  Proof.
    intros.
    destruct k, ec0, ec1; intuition; inversion H0; subst; apply R.L.
  Qed.
  
  Import R.
  Lemma dec_context_red_bot : 
      forall k ec v r, @dec_context ec k v = R.in_red r -> 
          forall ec' t', R.atom_plug t' ec' = R.atom_plug v ec ->  ~ k |~ ec' << ec.
  Proof with auto.
    intros. destruct k, ec0; dependent destruction v; inversion H; intro G; destruct ec'; inversion G.

subst. simpl in *. inversion H0; destruct v0; discriminate.

subst. simpl in *. inversion H0; destruct v0; discriminate.
  Qed.


  Lemma dec_context_val_bot : forall k ec v v', 
            dec_context ec k v = R.in_val v' -> forall ec', ~ k |~ ec' << ec.
  Proof.
    intros k ec v v' H ec' H0; 
    destruct k,ec; dependent destruction v; inversion H; destruct ec'; intuition.
  Qed.


  Lemma dec_term_ec_most_transitable : 
      forall {t0 ec0 t1 ec1 k},
          R.transitable_from k ec1 -> dec_term (R.atom_plug t1 ec1) k = R.in_term t0 ec0 ->
          R.transitable_from k ec0.
  Proof.
  destruct ec0, ec1, k;
  intuition; 
  inversion H0.
  Qed.


  Lemma eco_antirefl : forall k ec, ~ k |~ ec << ec.
  Proof.
    destruct k,ec0; intro H; destruct H.
  Qed.


  Lemma ec_order_antisym : forall k (ec ec0 : R.elem_context), 
      k |~ ec << ec0 -> ~ k |~ ec0 << ec.
  Proof.
    intros k ec ec0 H.
    destruct k, ec, ec0; inversion H; intro H0; inversion H0.
  Qed.

  Lemma ec_order_trans : forall k ec0 ec1 ec2,
      k |~ ec0 << ec1 -> k |~ ec1 << ec2 -> k |~ ec0 << ec2.
  Proof.
    intros.
    destruct k, ec0, ec1; inversion H;
    destruct ec2; inversion H0.
  Qed.

(*
  Ltac inj_vr := match goal with
  | [Hv : R.value_to_term _ = R.value_to_term _ |- _] => apply R.value_to_term_injective in Hv
  | [Hr : R.redex_to_term _ = R.redex_to_term _ |- _] => apply R.redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.*)

  (*Lemma elem_context_det : forall t0 t1 k ec0 ec1,
      k |~ ec0 << ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
      exists v : R.value (R.ckind_trans k ec1), t1 = R.value_to_term v.
  Proof.
    intros.
    destruct ec0; destruct ec1; inversion H0;
        inj_vr; subst;
    match goal with
    | _                            => contradiction (eco_antirefl _ _ H)
    | [ |- exists v0, _ ?v = _ v0] => exists v; reflexivity
    | [ H : (_ |~ _ << _) |- _]    => inversion H
    end.
  Qed.*)


  Lemma dec_context_term_next : 
      forall ec k v t ec', dec_context ec k v = R.in_term t ec' -> 
      k |~ ec' << ec /\ forall ec'', k |~ ec'' << ec -> ~ k |~ ec' << ec''.
  Proof with eauto.
    intros ec k v t ec' H.
    destruct k, ec, ec'; dependent destruction v; inversion H; subst;
    (
        split; 
        [ constructor
        | intros ec'' H0 H1; destruct ec''; inversion H0; inversion H1 ]
    ).
  Qed.


  Lemma ec_order_comp_if :
      forall ec0 ec1, R.ec_siblings ec0 ec1 -> 
      forall k, R.transitable_from k ec0 -> R.transitable_from k ec1 ->
      k |~ ec0 << ec1 \/ k |~ ec1 << ec0 \/ ec0 = ec1.
  Proof with eauto.
    intros ec0 ec1 H k H0 H1.
    destruct k, ec0, ec1; destruct H as (t1, (t2, H));
    inversion H; simpl; intuition; subst; 
    do 2 right; f_equal;
    compute in H1; intuition.
    apply R.valCa_to_term_injective...
    apply R.valCa_to_term_injective...
  Qed.

(*
  Lemma ec_order_comp_fi :
      forall ec0 ec1 k, k |~ ec0 << ec1 ->
      R.ec_siblings ec0 ec1 /\ R.transitable_from k ec0 /\ R.transitable_from k ec1.
  Proof with eauto.
    intuition.
    - destruct ec0, ec1;
          try inversion H.
      * exists e (R.value_to_term v)...
      * exists e (R.value_to_term v)...
    - intro; intuition.
    - intro; intuition.
  Qed.*)

  Lemma dec_term_liveness : 
      forall t k t0 ec0, dec_term t k = R.in_term t0 ec0 ->
      ~ R.dead_ckind (R.ckind_trans k ec0).
  Proof.
    intros.
    destruct t, k; inversion H; subst;
    auto.
  Qed.

End lc_ECCa_Ref.

Module lc_ECCa_REF_SEM := RedRefSem lc_ECCa_Ref.

(*Module MiniML_EAM := ProperEAMachine MiniML MiniML_REF_SEM. *)

Module lc_ECCa_Sem <: RED_SEM lc_ECCa.

  Import lc_ECCa.

  Inductive dec' : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=
  | d_CVar   : forall x {k1} (c : context k1 C) d
                (DCTX : decctx (vCVar x) c d),
                dec' (Var x) c d 
  | d_ECaVar : forall x {k1} (c : context k1 ECa) d
                (DCTX : decctx (vECaVar x) c d),
                dec' (Var x) c d 
  | d_CLam  : forall x t {k1} (c : context k1 C) d
                (DEC : dec' t (lam_c x =: c) d),
                dec' (Lam x t) c d
  | d_ECaLam : forall x t {k1} (c : context k1 ECa) d
                (DCTX : decctx (vECaLam x t) c d),
                dec' (Lam x t) c d
  | d_CApp   : forall t1 t2 {k1} (c : context k1 C) d
                (DEC  : dec' t1 (ap_r t2 =: c) d),
                dec' (App t1 t2) c d
  | d_ECaApp : forall t1 t2 {k1} (c : context k1 ECa) d
                (DEC  : dec' t1 (ap_r t2 =: c) d),
                dec' (App t1 t2) c d
  with decctx : forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
  | dc_em       : forall {k} (v : value k),
                   ~ dead_ckind k ->
                   decctx v [_] (d_val v)
  | dc_CAp_r1   : forall x t0 t {k1} (c : context k1 C),
                   decctx (vECaLam x t0) (ap_r t =: c) (d_red (rCApp x t0 t) c)
  | dc_CAp_r2   : forall x t {k1} (c : context k1 C) d
                   (DEC : dec' t (ap_l (vCaVar x) =: c) d),
                   decctx (vECaVar x) (ap_r t =: c) d
  | dc_CAp_r3   : forall v1 v2 t {k1} (c : context k1 C) d
                   (DEC : dec' t (ap_l (vCaApp v1 v2) =: c) d),
                   decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_ECaAp_r1 : forall x t0 t {k1} (c : context k1 ECa),
                   decctx (vECaLam x t0) (ap_r t =: c) (d_red (rECaApp x t0 t) c)
  | dc_ECaAp_r2 : forall x t {k1} (c : context k1 ECa) d
                   (DEC : dec' t (ap_l (vCaVar x) =: c) d),
                   decctx (vECaVar x) (ap_r t =: c) d
  | dc_ECaAp_r3 : forall v1 v2 t {k1} (c : context k1 ECa) d
                   (DEC : dec' t (ap_l (vCaApp v1 v2) =: c) d),
                   decctx (vECaApp v1 v2) (ap_r t =: c) d
  | dc_CAp_l    : forall v1 v2 {k1} (c : context k1 C) d
                   (DCTX : decctx (vCApp v1 v2) c d),
                   decctx v2 (ap_l v1 =: c) d
  | dc_ECaAp_l  : forall v1 v2 {k1} (c : context k1 ECa) d
                   (DCTX : decctx (vECaApp v1 v2) c d),
                   decctx v2 (ap_l v1 =: c) d
  | dc_CLam     : forall v x {k1} (c : context k1 C) d
                   (DCTX : decctx (vCLam x v) c d),
                   decctx v (lam_c x =: c) d.

  Definition dec t {k1 k2} (c : context k1 k2) d := dec' t c d.
  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dead_decctx_dead : forall k1 (c : context k1 CBot) v d, ~ decctx v c d.
  Proof.
  intros. intro.
  dependent destruction H.
  simpl in H.
  tauto.
  Qed.

  Ltac inj_vr := match goal with
  | [Hv : value_to_term _ = value_to_term _ |- _] => apply value_to_term_injective in Hv
  | [Hv : valCa_to_term _ = valCa_to_term _ |- _] => apply valCa_to_term_injective in Hv
  | [Hr : redex_to_term _ = redex_to_term _ |- _] => apply redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.

  Lemma L3 : forall x t y v, vECaLam x t <> vECaApp (vCaVar y) v.
  Proof.
  intros.
  intro.
  discriminate H.
  Qed.

  Lemma dec_val_self : forall {k2} (v : value k2) {k1} (c : context k1 k2) d, 
      dec (value_to_term v) c d <-> decctx v c d.
  Proof with auto. 
    induction v using val_Ind with
    (P := fun k2 (v : value k2) => forall (k1 : ckind) (c : context k1 k2)
              (d : decomp k1), dec v c d <-> decctx v c d)
    (P0:= fun v0 => forall (k1 k2 : ckind) (c : context k1 k2) (v : value k2)
              (d : decomp k1), (v0 : term) = (v : term) -> 
              (dec v c d <-> decctx v c d)); intros; 
    [ | | | | | | 
    | destruct v0; try discriminate; inversion H; repeat (inj_vr; subst); clear H 
    | destruct v1; try discriminate; inversion H; repeat (inj_vr; subst); clear H ]; 
    intros; split; intro H1;

    try solve [
      contradiction (dead_decctx_dead _ _ _ _ H1)

    | dependent destruction H1; auto;
      rewrite IHv in H1;
      dependent destruction H1;
      assumption

    | constructor; auto; 
      dependent destruction H1;
      rewrite IHv;
      constructor;
      constructor;
      assumption

    | match goal with v : valCa |- _ =>
      dependent destruction H1; auto;
      destruct L with v as (vc, H2); 
      rewrite H2 in H1;
      rewrite IHv in H1; auto;
      dependent destruction H1;
      destruct v; try discriminate;
      rewrite IHv0 in DEC;
      dependent destruction DEC;
      inversion H2; repeat (inj_vr; subst); 
      assumption
      end

    | match goal with v : valCa |- _ =>
      constructor; fold valCa_to_term; fold (@value_to_term C); auto;
      destruct L with v as (vc, H2);
      rewrite H2;
      apply IHv; auto;
      dependent destruction H1;
      destruct v; dependent destruction vc; try discriminate;
      constructor;
      apply IHv0;
      inversion H2; repeat (inj_vr; subst); 
      repeat constructor; auto
      end ].
  Qed.

  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall {k1 k2} (r : redex k2) (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof with auto.
    destruct r; intros; constructor;
    rewrite (dec_val_self (vECaLam v t)); constructor.
  Qed.

  Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = value_to_term v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), plug (redex_to_term r) c = t).
  Proof with auto with lc_ecca.
    induction t; intros.
    - destruct IHt1 with ECa as [(v1, H1) | (k2, (r1, (c1, H1)))]; auto;
      assert (G := IHt2 C id);
      clear IHt1 IHt2;
      subst.
      + dependent destruction v1; subst.
        * right. exists k1. destruct k1; simpl in H; try tauto; clear H;
          [ eexists (rCApp _ _ _), [_]
          | eexists (rECaApp _ _ _), [_] ];
          reflexivity.
        *{
          destruct G as [(v2, H1) | (k2, (r2, (c2, H1)))]; subst.
          - left. destruct k1; simpl in H; try tauto; clear H;
            [ exists (vCApp (vCaVar v) v2)
            | exists (vECaApp (vCaVar v) v2) ];
            auto.
          - right. destruct k1; simpl in H; try tauto; clear H;
            [ exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: (@empty C))
            | exists k2 r2 (c2 ~+ ap_l (vCaVar v) =: (@empty ECa)) ];
            simpl; rewrite plug_compose; auto. }
        * {
          destruct G as [(v2, H1) | (k2, (r2, (c2, H1)))]; subst.
          - left. destruct k1; simpl in H; try tauto; clear H;
            [ exists (vCApp (vCaApp v v1) v2)
            | exists (vECaApp (vCaApp v v1) v2) ];
            auto.
          - right. destruct k1; simpl in H; try tauto; clear H;
            [ exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: (@empty C))
            | exists k2 r2 (c2 ~+ ap_l (vCaApp v v1) =: (@empty ECa)) ];
            rewrite plug_compose; auto. }
      + right. destruct k1; simpl in H; try tauto; clear H;
        [ exists k2 r1 (c1 ~+ ap_r t2 =: (@empty C))
        | exists k2 r1 (c1 ~+ ap_r t2 =: (@empty ECa)) ];
        rewrite plug_compose; auto.
    - left. destruct k1; simpl in H; try tauto; clear H;
      [ exists (vCVar v)
      | exists (vECaVar v) ];
      auto.
    - destruct k1; simpl in H; try tauto; clear H.
      + destruct (IHt C) as [(v1, H) | (k, (r1, (c, H)))]; subst...
        * left. exists (vCLam v v1)...
        * right. exists k r1 (c ~+ lam_c v =: (@empty C)).
          rewrite plug_compose; auto.
      + left. exists (vECaLam v t)...
    Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall t k1 k2 (c : context k1 k2) d, dec t c d -> 
                          decomp_to_term d = plug t c.
  Proof.
    induction 1 using dec_Ind with
    (P := fun t _ _ c d (H:dec t c d) => decomp_to_term d = plug t c)
    (P0 := fun _ v _ c d (H:decctx v c d) => decomp_to_term d = plug (value_to_term v) c);
    intros; simpl; auto.
  Qed.

  Include RED_LANG_Facts lc_ECCa.

  Lemma dec_plug : forall k1 k2 (c : context k1 k2) k3 (c0 : context k3 k1) t d, 
                          ~ dead_ckind k2 -> dec (plug t c) c0 d -> 
                          dec t (c ~+ c0) d.
  Proof.
    induction c; simpl; auto; destruct ec0;
    intros ? c0 t0 d H DEC; assert (hh := IHc _ _ _ _ (context_tail_liveness _ _ H) DEC);
    dependent destruction hh; subst; auto; simpl in H; try tauto;
      destruct (L v);
      rewrite H0 in hh; rewrite dec_val_self in hh;
      dependent destruction hh; destruct v; try discriminate; 
      inversion H0; repeat (inj_vr; subst); auto.
  Qed.

  Lemma dec_plug_rev : forall k1 k2 (c : context k1 k2) k3 (c0 : context k3 k1) t d, 
                          ~ dead_ckind k2 ->  dec t (c ~+ c0) d -> 
                          dec (plug t c) c0 d.
  Proof.
    induction c; simpl; auto; destruct ec0; intros; apply IHc;
    try solve [ eapply context_tail_liveness; eauto ];
    destruct k2; simpl in H; try tauto; try solve [constructor; auto];
      destruct (L v);
      simpl; constructor; rewrite H1;
      apply dec_val_self;
      destruct v; dependent destruction x; try discriminate H1; 
      inversion H1; repeat (inj_vr; subst);
      constructor; auto.
  Qed.

  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall (t : term) {k} (d : decomp k), dec t (@empty k) d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k} (r : redex k) t {k'} (c : context k' k) d v,
              contract r = Some t -> decempty (plug t c) d -> iter d v ->
              iter (d_red r c) v.

  Inductive eval : term -> forall {k}, value k -> Prop :=
  | e_intro : forall t {k} (d : decomp k) v, decempty t d -> iter d v -> eval t v.

End lc_ECCa_Sem.

Lemma dec_sem_ref : forall t k1 k2 (c : lc_ECCa.context k1 k2) d, 
                        lc_ECCa_Sem.dec t c d -> lc_ECCa_REF_SEM.dec t c d.
Proof.
  induction 1 using lc_ECCa_Sem.dec_Ind with
  (P := fun t _ _ c d (H : lc_ECCa_Sem.dec t c d) => lc_ECCa_REF_SEM.dec t c d)
  (P0:= fun _ v _ c d (H : lc_ECCa_Sem.decctx v c d) => lc_ECCa_REF_SEM.decctx v c d);
  try solve 
  [ econstructor; simpl; eauto
  | econstructor 3; simpl; eauto
  | eapply (@lc_ECCa_REF_SEM.dc_dec)  with (ec:=lc_ECCa.ap_r t)(k2:= lc_ECCa.C); simpl; auto
  | eapply (@lc_ECCa_REF_SEM.dc_term) with (ec:=lc_ECCa.ap_r t)(k2:= lc_ECCa.C); simpl; eauto 
  | eapply (@lc_ECCa_REF_SEM.dc_dec)  with (ec:=lc_ECCa.ap_r t)(k2:= lc_ECCa.ECa); simpl; auto
  | eapply (@lc_ECCa_REF_SEM.dc_term) with (ec:=lc_ECCa.ap_r t)(k2:= lc_ECCa.ECa); simpl; eauto
  | eapply (@lc_ECCa_REF_SEM.dc_val)  with (ec:=lc_ECCa.ap_l v1)(k2:= lc_ECCa.C); simpl; auto
  | eapply (@lc_ECCa_REF_SEM.dc_val)  with (ec:=lc_ECCa.ap_l v1)(k2:= lc_ECCa.ECa); simpl; auto
  | eapply (@lc_ECCa_REF_SEM.dc_val)  with (ec:=lc_ECCa.lam_c x)(k2:= lc_ECCa.C); simpl; auto
].
Qed.
Hint Resolve dec_sem_ref.
 
Lemma dec_ref_sem : forall t k1 k2 (c : lc_ECCa.context k1 k2) d, 
                        lc_ECCa_REF_SEM.dec t c d -> lc_ECCa_Sem.dec t c d.
Proof.
  induction 1 using lc_ECCa_REF_SEM.dec_Ind with
  (P := fun t _ _ c d (H : lc_ECCa_REF_SEM.dec t c d) => lc_ECCa_Sem.dec t c d)
  (P0:= fun _ v _ c d (H : lc_ECCa_REF_SEM.decctx v c d) => lc_ECCa_Sem.decctx v c d);
  try (destruct t, k2); try inversion e; subst;
  try solve 
  [ discriminate 
  | constructor; auto 
  | destruct ec; try destruct k2; dependent destruction v; inversion e; subst; constructor; auto ].
Qed.
Hint Resolve dec_ref_sem.

Lemma iter_sem_ref : forall k (d : lc_ECCa.decomp k) v, 
                         lc_ECCa_Sem.iter d v <-> lc_ECCa_REF_SEM.RS.iter d v.
Proof with eauto with lc_ecca.
split; intros H; dependent induction H; subst; simpl in *; auto; try solve [constructor];
dependent destruction H0; econstructor 2; simpl in *; eauto; constructor; first [apply dec_sem_ref | apply dec_ref_sem]; eauto.
Qed.

Lemma eval_sem_ref : forall t k (v : lc_ECCa.value k), 
                         lc_ECCa_Sem.eval t v <-> lc_ECCa_REF_SEM.RS.eval t v.
Proof with auto.
split; intro H; dependent destruction H; econstructor;
try solve 
[ apply iter_sem_ref; eauto
| destruct H; constructor; first [apply dec_sem_ref | apply dec_ref_sem]; eauto ].
Qed.

Module MiniML_Machine <: ABSTRACT_MACHINE.

Definition term := MiniML.term.
Definition value := MiniML.value.

Definition configuration := MiniML_EAM.configuration.
Definition c_init := MiniML_EAM.c_init.
Definition c_final := MiniML_EAM.c_final.
Definition c_eval := MiniML_EAM.c_eval.
Definition c_apply := MiniML_EAM.c_apply.

Notation " [ a ] " := (c_init a) (at level 60, no associativity).
Notation " [: a :] " := (c_final a) (at level 60).
Notation " [ a , b ] " := (c_eval a b) (at level 60).
Notation " [: a , b :] " := (c_apply a b) (at level 60).

Reserved Notation " a → b " (at level 40).

Inductive trans : configuration -> configuration -> Prop :=
| t_init : forall t,           [ t ] →  [t, MiniML.empty]
| t_final: forall v,           [: MiniML.empty, v :] → [: v :]
| t_ez   : forall c,           [MiniML.Z, c] → [: c, MiniML.vZ :]
| t_es   : forall t c,         [MiniML.S t, c] → [t, MiniML.s_c :: c]
| t_evar : forall x c,         [MiniML.Var x, c] → [: c, MiniML.vVar x :]
| t_elam : forall x t c,       [MiniML.Lam x t, c] → [: c, MiniML.vLam x t :]
| t_eapp : forall t1 t2 c,     [MiniML.App t1 t2, c] → [t1, MiniML.ap_r t2 :: c]
| t_ecas : forall t ez x es c, [MiniML.Case t ez x es, c] → [t, MiniML.case_c ez x es :: c]
| t_efix : forall x t t0 c
             (CTR : MiniML.contract (MiniML.rFix x t) = Some t0),
             [MiniML.Fix x t, c] → [t0, c]
| t_elet : forall x t e c,     [MiniML.Letv x t e, c] → [t, MiniML.let_c x e :: c]
| t_epar : forall t1 t2 c,     [MiniML.Pair t1 t2, c] → [t1, MiniML.pair_r t2 :: c]
| t_efst : forall t c,         [MiniML.Fst t, c] → [t, MiniML.fst_c :: c]
| t_esnd : forall t c,         [MiniML.Snd t, c] → [t, MiniML.snd_c :: c]
| t_as   : forall v c,         [: MiniML.s_c :: c, v :] → [: c, MiniML.vS v :]
| t_aa_r : forall v t c,       [: MiniML.ap_r t :: c, v :] → [t, MiniML.ap_l v :: c]
| t_aa_l : forall v v0 t c
             (CTR : MiniML.contract (MiniML.rApp v0 v) = Some t),
             [: MiniML.ap_l v0 :: c, v :] → [t, c]
| t_acas : forall v ez x es c t
             (CTR : MiniML.contract (MiniML.rCase v ez x es) = Some t),
             [: MiniML.case_c ez x es :: c, v :] → [t, c]
| t_alet : forall v x e c t
             (CTR : MiniML.contract (MiniML.rLet x v e) = Some t),
             [: MiniML.let_c x e :: c, v :] → [t, c]
| t_ap_r : forall v t c,       [: MiniML.pair_r t :: c, v :] → [t, MiniML.pair_l v :: c]
| t_ap_l : forall v v0 c,      [: MiniML.pair_l v0 :: c, v :] → [: c, MiniML.vPair v0 v :]
| t_afst : forall v c t
             (CTR : MiniML.contract (MiniML.rFst v) = Some t),
             [: MiniML.fst_c :: c, v :] → [t, c]
| t_asnd : forall v c t
             (CTR : MiniML.contract (MiniML.rSnd v) = Some t),
             [: MiniML.snd_c :: c, v :] → [t, c]
where " a → b " := (trans a b).
Definition transition := trans.

Notation " a >> b " := (MiniML_EAM.transition a b) (at level 40).
Notation " a >>+ b " := (MiniML_EAM.AM.trans_close a b) (at level 40).

Reserved Notation " a →+ b " (at level 40, no associativity).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall c0 c1 (STEP : c0 → c1), c0 →+ c1
| multi_step : forall c0 c1 c2 (STEP : c0 → c1) (REC : c1 →+ c2), c0 →+ c2
where " a →+ b " := (trans_close a b).

Inductive eval : term -> value -> Prop :=
| e_intro : forall t v (TC : [ t ] →+ [: v :]), eval t v.

Lemma trans_eam_mlm : forall c0 c1, c0 >> c1 -> c0 → c1.
Proof with auto.
  intros c0 c1 T; inversion T; subst; match goal with
  | [ DT : MiniML_EAM.dec_term ?t = ?int |- _ ] => destruct t; inversion DT
  | [ DC : MiniML_EAM.dec_context ?ec ?v = ?int |- _ ] => destruct ec; inversion DC
  | [ |- _ ] => idtac
  end; subst; constructor...
Qed.
Hint Resolve trans_eam_mlm.

Lemma tcl_eam_mlm : forall c0 c1, c0 >>+ c1 -> c0 →+ c1.
Proof with eauto.
  intros c0 c1 TC; induction TC; subst; unfold MiniML_EAM.AM.transition in *;
  [econstructor | econstructor 2]...
Qed.

Lemma eval_eam_mlm : forall t v, MiniML_EAM.AM.eval t v -> eval t v.
Proof.
  intros t v E; inversion_clear E; constructor; apply tcl_eam_mlm; auto.
Qed.

Lemma trans_mlm_eam : forall c0 c1, c0 → c1 -> c0 >> c1.
Proof with auto.
  intros w w' H; inversion H; subst; econstructor; simpl...
Qed.
Hint Resolve trans_mlm_eam.

Lemma tcl_mlm_eam : forall c0 c1, c0 →+ c1 -> c0 >>+ c1.
Proof with eauto.
  induction 1; subst; [econstructor | econstructor 2]; unfold MiniML_EAM.AM.transition...
Qed.

Lemma eval_mlm_eam : forall t v, eval t v -> MiniML_EAM.AM.eval t v.
Proof.
  intros t v E; inversion_clear E; constructor; apply tcl_mlm_eam; auto.
Qed.

Theorem MiniML_Machine_correct : forall t v, MiniML_Sem.eval t v <-> eval t v.
Proof.
  intros; rewrite eval_sem_ref; rewrite MiniML_EAM.eval_apply_correct;
  split; [apply eval_eam_mlm | apply eval_mlm_eam].
Qed.

End MiniML_Machine.*)
