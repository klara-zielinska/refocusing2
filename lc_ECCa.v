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

Inductive _ckind := C | ECa | Ca | CBot.
Definition ckind := _ckind.

Inductive val : ckind -> Set :=

| vCLam : v_name -> val C -> val C
| vCVar : v_name -> val C
| vCApp : val Ca -> val C -> val C

| vECaLam : v_name -> term -> val ECa
| vECaVar : v_name -> val ECa
| vECaApp : val Ca -> val C -> val ECa

| vCaVar : v_name -> val Ca
| vCaApp : val Ca -> val C -> val Ca.

Definition value := val.

Inductive red : ckind -> Set :=
| rCApp   : v_name -> term -> term -> red C
| rECaApp : v_name -> term -> term -> red ECa.
Definition redex := red.

Inductive ec :=
| lam_c : v_name -> ec
| ap_r  : term -> ec
| ap_l  : value Ca -> ec.
Definition elem_context := ec.

Definition ckind_trans (k : ckind) (ec : elem_context) := 
match k with
| C    => match ec with lam_c _ => C    | ap_r _ => ECa | ap_l _ => C end
| ECa  => match ec with lam_c _ => CBot | ap_r _ => ECa | ap_l _ => C end
| _    => CBot
end.
Definition init_ckind : ckind := C.
Definition dead_ckind (k : ckind) := match k with CBot | Ca => True | _ => False end.

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
| vCApp v1 v2 => App (value_to_term v1) (value_to_term v2)
| vECaLam x t => Lam x t
| vECaVar x => Var x
| vECaApp v1 v2 => App (value_to_term v1) (value_to_term v2)
| vCaVar x => Var x
| vCaApp v1 v2 => App (value_to_term v1) (value_to_term v2)
end.
Coercion value_to_term : value >-> term.


Definition redex_to_term {k} (r : redex k) : term :=
match r with
| rCApp x t1 t2 => App (Lam x t1) t2
| rECaApp x t1 t2 => App (Lam x t1) t2
end.
Coercion redex_to_term : redex >-> term.


Lemma value_to_term_injective : 
    forall k (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

Proof with auto.
dependent induction v; dependent destruction v'; intro H; inversion H; f_equal...
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

  Definition only_empty (t : term) (k : ckind) : Prop := 
      forall t' k' (c : context k k'), ~ dead_ckind k' -> plug t' c = t -> k = k' /\ c ~= @empty k.

  Definition only_trivial (t : term) (k : ckind) : Prop := 
      forall t' k' (c : context k k'), ~ dead_ckind k' -> plug t' c = t -> 
          k = k' /\ c ~= @empty k \/ exists (v : value k'), t' = value_to_term v.


Lemma L : forall v1 : value Ca, exists v2 : value ECa, (v1 : term) = (v2 : term).
Proof with auto.
dependent destruction v1; intros.
- exists (vECaVar v)...
- exists (vECaApp v1_1 v1_2)...
Qed.

  Lemma value_trivial : forall k (v : value k), only_trivial (value_to_term v) k.
  Proof with auto.
    intros k1 v t k2 c H; revert t.
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
            try solve [contradiction H; compute; trivial]; 
            dependent_destruction2 Hv
      end;
      try solve [eexists; eauto | apply L]...
  Qed.

  Lemma redex_trivial : forall k (r : redex k), only_trivial (redex_to_term r) k.
  Proof with auto.
    intros k1 r t k2 c H; revert t.
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
            try solve [contradiction H; compute; trivial]; 
            dependent_destruction2 Hvr
      end; simpl in *; 
      try solve [ exists (vECaLam v t1); auto 
                | dependent destruction v; discriminate
                | eexists; eauto
                | apply L].
  Qed.

  Lemma value_redex : forall k (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof with auto.
    destruct v; destruct r; intro H; try dependent destruction v1; try discriminate H. 
  Qed.

  Lemma ot_subt : 
      forall t t0 ec k, ~ dead_ckind (ckind_trans k ec) ->
                        only_trivial t k -> atom_plug t0 ec = t -> 
          exists v : value (ckind_trans k ec), t0 = value_to_term v.

  Proof with auto.
    intros.
    destruct (H0 t0 _ (ec0 =: [_])) as [(H2, H3) | (v, H2)]...
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

Lemma L2 : forall t ec k, ~ dead_ckind (ckind_trans k ec) ->
               only_trivial (atom_plug t ec) k -> only_trivial t (ckind_trans k ec).
Proof with eauto.
intros.
intros t' k' c H1 H2.
destruct (H0 t' k' (c ~+ ec0 =: [_])) as [(H3, H4) | ?]... rewrite plug_compose... subst...
absurd_hyp H4... revert H3; clear; intro. dependent induction c; intro H; discriminateJM H.
Qed.


  Lemma trivial_val_red : 
      forall k (t : term), ~ dead_ckind k -> only_trivial t k ->
         (exists (v : value k), t = value_to_term v) \/
         (exists (r : redex k), t = redex_to_term r).

  Proof with auto.
    intros. revert k H H0.
    induction t; intros;
    destruct k; try solve [contradiction H; simpl; auto].
    Focus 5. 
    destruct (ot_subt _ t (lam_c v) C H H0); eauto; subst;
    left; exists (vCLam v x); subst...
    Focus 5.
    left; exists (vECaLam v t)...

    Focus 3.
    left; exists (vCVar v)...
    Focus 3.
    left; exists (vECaVar v)...

    Focus 1.
    destruct (ot_subt _ t1 (ap_r t2) C H H0); eauto; subst.
    dependent destruction x.
    right. exists (rCApp v t t2)...
    destruct (ot_subt _ t2 (ap_l (vCaVar v)) C H H0); eauto; subst.
    left. exists (vCApp (vCaVar v) x0)...
    destruct (ot_subt _ t2 (ap_l (vCaApp x1 x2)) C H H0); eauto; subst.
    left. exists (vCApp (vCaApp x1 x2) x0)...

    destruct (ot_subt _ t1 (ap_r t2) ECa H H0); eauto; subst.
    dependent destruction x.
    right. exists (rECaApp v t t2)...
    destruct (ot_subt _ t2 (ap_l (vCaVar v)) ECa H H0); eauto; subst.
    left. exists (vECaApp (vCaVar v) x0)...
    destruct (ot_subt _ t2 (ap_l (vCaApp x1 x2)) ECa H H0); eauto; subst.
    left. exists (vECaApp (vCaApp x1 x2) x0)...
  Qed.

  Lemma proper_death : forall k, dead_ckind k -> 
                           ~ exists k' (c : context k k') (r : redex k'), True.
  Proof.
  destruct k;
  intuition;
  destruct H0 as (k', (c, (r, _)));
  cut (k' = Ca \/ k' = CBot);
  solve [ intro H0; destruct H0; subst; dependent destruction r
        | clear r; dependent induction c; auto; 
          destruct IHc; auto; subst; auto ].
  Qed.

End lc_ECCa.


Module lc_ECCa_Ref <: RED_REF_LANG.

  Module R := lc_ECCa.

  Definition dec_term (t : R.term) k : ~ R.dead_ckind k -> R.interm_dec k.
  intro H.
  refine (
      match k as k0 return ~ R.dead_ckind k0 -> R.interm_dec k0 with 
      | R.C =>   fun _ => match t with
                          | R.App t1 t2 => R.in_term t1 (R.ap_r t2)
                          | R.Var x     => R.in_val (R.vCVar x)
                          | R.Lam x t1  => R.in_term t1 (R.lam_c x)
                          end
      | R.ECa => fun _ => match t with
                          | R.App t1 t2 => R.in_term t1 (R.ap_r t2)
                          | R.Var x     => R.in_val (R.vECaVar x)
                          | R.Lam x t1  => R.in_val (R.vECaLam x t1)
                          end
      | R.Ca   => fun H0 => _
      | R.CBot => fun H0 => _
      end H
  );
  simpl in H0; intuition.
  Defined.

  Definition dec_context (ec : R.elem_context) k (v : R.value (R.ckind_trans k ec)) 
                 : R.interm_dec k :=
  match ec with
  | R.s_c            =>  R.in_val (R.vS v)
  | R.ap_l v0        =>  R.in_red (R.rApp v0 v)
  | R.ap_r t         =>  R.in_term t (R.ap_l v)
  | R.case_c ez x es =>  R.in_red (R.rCase v ez x es)
  | R.let_c x e      =>  R.in_red (R.rLet x v e)
  | R.fst_c          =>  R.in_red (R.rFst v)
  | R.snd_c          =>  R.in_red (R.rSnd v)
  | R.pair_l v0      =>  R.in_val (R.vPair v0 v)
  | R.pair_r t       =>  R.in_term t (R.pair_l v)
  end.

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
  match ec, ec0 with
  | R.ap_l _, R.ap_r _ => True
  | R.pair_l _, R.pair_r _ => True
  | _, _ => False
  end.
  Notation "k |~  a << b " := (ec_order k a b) (at level 40, no associativity).
  Lemma wf_eco : forall k, well_founded (ec_order k).
  Proof.
    prove_ec_wf.
  Qed.


  Lemma dec_term_red_empty : forall t k (r : R.redex k), 
                                 dec_term t k = R.in_red r -> R.only_empty t k.
  Proof with auto.
    intros t k r H.
    destruct t; inversion H; subst; clear H.
    intros t0 k' c; generalize dependent t0.
    induction c;
        intros; simpl in *.
    - intuition.
    - destruct (IHc _ H) as (H0, H1);
          subst; dependent destruction H1.
      destruct ec; inversion H.
  Qed.


  Lemma dec_term_val_empty : forall t k (v : R.value k), 
                                 dec_term t k = R.in_val v -> R.only_empty t k.
  Proof with auto.
    intros t k r H.
    destruct t; inversion H; subst; clear H;
    intros t0 k' c; generalize dependent t0;
    (
        induction c;
            intros; simpl in *;
        [ intuition
        | destruct (IHc _ H) as (H0, H1);
              subst; dependent destruction H1;
          destruct ec; inversion H ]
    ).
  Qed.


  Lemma dec_term_term_top : forall t t' k ec, 
            dec_term t k = R.in_term t' ec -> forall ec', ~ k |~ ec << ec'.
  Proof.
    intros t t' k ec H ec' H0; destruct t; inversion H; subst; destruct ec'; inversion H0.
  Qed.


  Lemma dec_context_red_bot : forall k ec v r, 
            dec_context ec k v = R.in_red r -> forall ec', ~ k |~ ec' << ec.
  Proof with auto.
    intros k ec v r H ec' H0; destruct ec; inversion H; destruct ec'; inversion H0.
  Qed.


  Lemma dec_context_val_bot : forall k ec v v', 
            dec_context ec k v = R.in_val v' -> forall ec', ~ k |~ ec' << ec.
  Proof.
    intros k ec v v' H ec' H0; destruct ec; inversion H; destruct ec'; inversion H0.
  Qed.


  Lemma dec_term_ec_most_transitable : 
      forall {t0 ec0 t1 ec1 k},
          R.transitable_from k ec1 -> dec_term (R.atom_plug t1 ec1) k = R.in_term t0 ec0 ->
          R.transitable_from k ec0.
  Proof.
  intuition.
  Qed.


  Lemma eco_antirefl : forall k ec, ~ k |~ ec << ec.
  Proof.
    destruct ec; intro H; destruct H.
  Qed.


  Lemma ec_order_antisym : forall k (ec ec0 : R.elem_context), 
      k |~ ec << ec0 -> ~ k |~ ec0 << ec.
  Proof.
    intros k ec ec0 H; destruct ec; destruct ec0; inversion H; subst; intro H0; inversion H0.
  Qed.

  Lemma ec_order_trans : forall k ec0 ec1 ec2,
      k |~ ec0 << ec1 -> k |~ ec1 << ec2 -> k |~ ec0 << ec2.
  Proof.
    intros.
    destruct ec0, ec1; inversion H;
    destruct ec2; inversion H0.
  Qed.


  Ltac inj_vr := match goal with
  | [Hv : R.value_to_term _ = R.value_to_term _ |- _] => apply R.value_to_term_injective in Hv
  | [Hr : R.redex_to_term _ = R.redex_to_term _ |- _] => apply R.redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.

  Lemma elem_context_det : forall t0 t1 k ec0 ec1,
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
  Qed.


  Lemma dec_context_term_next : 
      forall ec k v t ec', dec_context ec k v = R.in_term t ec' -> 
      k |~ ec' << ec /\ forall ec'', k |~ ec'' << ec -> ~ k |~ ec' << ec''.
  Proof with eauto.
    intros ec k v t ec' H.
    destruct ec; inversion H; subst;
    (
        split; 
        [ constructor
        | intros ec'' H0 H1; destruct ec''; inversion H0; inversion H1 ]
    ).
  Qed.


  Lemma dec_term_correct : forall t k, match dec_term t k with
      | R.in_red r => R.redex_to_term r = t
      | R.in_val v => R.value_to_term v = t
      | R.in_term t' ec => R.atom_plug t' ec = t
      end.
  Proof.
    destruct t; simpl; auto.
  Qed.


  Lemma dec_context_correct : forall ec k v, match dec_context ec k v with
      | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
      | R.in_val v' => R.value_to_term v' = R.atom_plug (R.value_to_term v) ec
      | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
      end.
  Proof.
    destruct ec; simpl; destruct k; auto.
  Qed.


  Lemma ec_order_comp_if :
      forall ec0 ec1, R.ec_siblings ec0 ec1 -> 
      forall k, R.transitable_from k ec0 -> R.transitable_from k ec1 ->
      k |~ ec0 << ec1 \/ k |~ ec1 << ec0 \/ ec0 = ec1.
  Proof with eauto.
    intros ec0 ec1 H k H0 H1.
    destruct ec0; destruct ec1; destruct H as (t0, (t1, H)); inversion H; inj_vr; subst;
    intuition constructor.
  Qed.


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
  Qed.

End MiniMLRef.

Module MiniML_REF_SEM := RedRefSem MiniMLRef.

(*Module MiniML_EAM := ProperEAMachine MiniML MiniML_REF_SEM.

Module MiniML_Sem <: RED_SEM MiniML.

  Inductive dec' : MiniML.term -> MiniML.context -> MiniML.decomp -> Prop :=
  | d_z   : forall c d
              (DCTX : decctx MiniML.vZ c d),
              dec' MiniML.Z c d
  | d_s   : forall t c d
              (DEC  : dec' t (MiniML.s_c :: c) d),
              dec' (MiniML.S t) c d
  | d_case: forall t ez x es c d
              (DEC  : dec' t (MiniML.case_c ez x es :: c) d),
              dec' (MiniML.Case t ez x es) c d
  | d_var : forall x c d
              (DCTX : decctx (MiniML.vVar x) c d),
              dec' (MiniML.Var x) c d
  | d_lam : forall x t c d
              (DCTX : decctx (MiniML.vLam x t) c d),
              dec' (MiniML.Lam x t) c d
  | d_app : forall t1 t2 c d
              (DEC  : dec' t1 (MiniML.ap_r t2 :: c) d),
              dec' (MiniML.App t1 t2) c d
  | d_let : forall x t e c d
              (DEC  : dec' t (MiniML.let_c x e :: c) d),
              dec' (MiniML.Letv x t e) c d
  | d_fix : forall x t c,
              dec' (MiniML.Fix x t) c (MiniML.d_red (MiniML.rFix x t) c)
  | d_pair: forall t1 t2 c d
              (DEC  : dec' t1 (MiniML.pair_r t2 :: c) d),
              dec' (MiniML.Pair t1 t2) c d
  | d_fst : forall t c d
              (DEC  : dec' t (MiniML.fst_c :: c) d),
              dec' (MiniML.Fst t) c d
  | d_snd : forall t c d
              (DEC  : dec' t (MiniML.snd_c :: c) d),
              dec' (MiniML.Snd t) c d
  with decctx : MiniML.value -> MiniML.context -> MiniML.decomp -> Prop :=
  | dc_em : forall v,
              decctx v MiniML.empty (MiniML.d_val v)
  | dc_s  : forall v c d
              (DCTX : decctx (MiniML.vS v) c d),
              decctx v (MiniML.s_c :: c) d
  | dc_cs : forall v x ez es c,
              decctx v (MiniML.case_c ez x es :: c) (MiniML.d_red (MiniML.rCase v ez x es) c)
  | dc_apr: forall v t c d
              (DEC  : dec' t (MiniML.ap_l v :: c) d),
              decctx v (MiniML.ap_r t :: c) d
  | dc_apl: forall v v0 c,
              decctx v (MiniML.ap_l v0 :: c) (MiniML.d_red (MiniML.rApp v0 v) c)
  | dc_let: forall v x e c,
              decctx v (MiniML.let_c x e :: c) (MiniML.d_red (MiniML.rLet x v e) c)
  | dc_p_r: forall t v c d
              (DEC  : dec' t (MiniML.pair_l v :: c) d),
              decctx v (MiniML.pair_r t :: c) d
  | dc_p_l: forall v v0 c d
              (DCTX : decctx (MiniML.vPair v0 v) c d),
              decctx v (MiniML.pair_l v0 :: c) d
  | dc_fst: forall v c,
              decctx v (MiniML.fst_c :: c) (MiniML.d_red (MiniML.rFst v) c)
  | dc_snd: forall v c,
              decctx v (MiniML.snd_c :: c) (MiniML.d_red (MiniML.rSnd v) c).
  Definition dec := dec'.
  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dec_val_self : forall v c d, dec (MiniML.value_to_term v) c d <-> decctx v c d.
  Proof with auto.
    induction v;(intros; split; intro H;
    [ inversion H; subst; auto; try rewrite IHv in DEC; try rewrite IHv1 in DEC; inversion DEC; auto; rewrite IHv2 in DEC0; inversion DEC0; subst
    | constructor; auto; try rewrite IHv; try rewrite IHv1; constructor; auto; rewrite IHv2; constructor])...
  Qed.

  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall (r : MiniML.redex) (c : MiniML.context), dec (MiniML.redex_to_term r) c (MiniML.d_red r c).
  Proof with auto.
    induction r; intros; constructor; rewrite dec_val_self; constructor; rewrite dec_val_self; constructor.
  Qed.

  Lemma decompose : forall t : MiniML.term, (exists v:MiniML.value, t = MiniML.value_to_term v) \/
      (exists r:MiniML.redex, exists c:MiniML.context, MiniML.plug (MiniML.redex_to_term r) c = t).
  Proof with auto with miniml.
    induction t.
    left; exists MiniML.vZ...
    destruct IHt as [[v H] | [r [c H]]]; [left; exists (MiniML.vS v) | right; exists r; exists (c ++ (MiniML.s_c :: nil))];
    subst; simpl; unfold MiniML.plug; auto; apply fold_left_app.
    right; destruct IHt1 as [[v1 H] | [r1 [c1 H]]]; [destruct IHt2 as [[v2 H2] | [r2 [c2 H2]]];
    [exists (MiniML.rApp v1 v2); exists MiniML.empty | exists r2; exists (c2 ++ (MiniML.ap_l v1 :: MiniML.empty))] |
    exists r1; exists (c1 ++ (MiniML.ap_r t2 :: MiniML.empty))]; simpl; subst; auto; unfold MiniML.plug; apply fold_left_app.
    left; exists (MiniML.vVar v)...
    left; exists (MiniML.vLam v t)...
    clear IHt2 IHt3; destruct IHt1 as [[v1 H] | [r [c H]]]; [ right; exists (MiniML.rCase v1 t2 v t3); exists MiniML.empty |
    right; exists r; exists (c ++ (MiniML.case_c t2 v t3 :: MiniML.empty))]; subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    clear IHt2; destruct IHt1 as [[v1 H] | [r [c H]]]; [right; exists (MiniML.rLet v v1 t2); exists MiniML.empty | right;
    exists r; exists (c ++ (MiniML.let_c v t2 :: MiniML.empty))]; subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    clear IHt; right; exists (MiniML.rFix v t); exists MiniML.empty; simpl; auto.
    destruct IHt1 as [[v1 H1] | [r1 [c1 H1]]]; [destruct IHt2 as [[v2 H2] | [r2 [c2 H2]]]; [left; exists (MiniML.vPair v1 v2) |
    right; exists r2; exists (c2 ++ (MiniML.pair_l v1 :: nil))] | right; exists r1; exists (c1 ++ (MiniML.pair_r t2 :: nil))];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    destruct IHt as [[v H] | [r [c H]]]; right; [ exists (MiniML.rFst v); exists MiniML.empty | exists r; exists (c ++ (MiniML.fst_c :: nil)) ];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    destruct IHt as [[v H] | [r [c H]]]; right; [ exists (MiniML.rSnd v); exists MiniML.empty | exists r; exists (c ++ (MiniML.snd_c :: nil)) ];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
  Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall t c d, dec t c d -> MiniML.decomp_to_term d = MiniML.plug t c.
  Proof.
    induction 1 using dec_Ind with
    (P := fun t c d (H:dec t c d) => MiniML.decomp_to_term d = MiniML.plug t c)
    (P0 := fun v c d (H:decctx v c d) => MiniML.decomp_to_term d = MiniML.plug (MiniML.value_to_term v) c); intros; simpl; auto.
  Qed.

  Lemma dec_plug : forall c c0 t d, dec (MiniML.plug t c) c0 d -> dec t (MiniML.compose c c0) d.
  Proof.
    induction c; simpl; auto; destruct a; intros c0 t0 d DEC; assert (hh := IHc _ _ _ DEC); 
    inversion hh; subst; auto; rewrite dec_val_self in DEC0; inversion DEC0; subst; auto.
  Qed.

  Lemma dec_plug_rev : forall c c0 t d, dec t (MiniML.compose c c0) d -> dec (MiniML.plug t c) c0 d.
  Proof.
    induction c; simpl; auto; destruct a; intros; apply IHc;
    repeat (constructor; simpl; auto; try rewrite dec_val_self).
  Qed.

  Inductive decempty : MiniML.term -> MiniML.decomp -> Prop :=
  | d_intro : forall t d (DEC : dec t MiniML.empty d), decempty t d.

  Inductive iter : MiniML.decomp -> MiniML.value -> Prop :=
  | i_val : forall v, iter (MiniML.d_val v) v
  | i_red : forall r t c d v
              (CONTR : MiniML.contract r = Some t)
              (D_EM  : decempty (MiniML.plug t c) d)
              (R_IT  : iter d v),
              iter (MiniML.d_red r c) v.

  Inductive eval : MiniML.term -> MiniML.value -> Prop :=
  | e_intro : forall t d v
                (D_EM : decempty t d)
                (ITER : iter d v),
                eval t v.

End MiniML_Sem.

Lemma dec_sem_ref : forall t c d, MiniML_Sem.dec t c d -> MiniML_REF_SEM.dec t c d.
Proof.
  induction 1 using MiniML_Sem.dec_Ind with
  (P := fun t c d (H : MiniML_Sem.dec t c d) => MiniML_REF_SEM.dec t c d)
  (P0:= fun v c d (H : MiniML_Sem.decctx v c d) => MiniML_REF_SEM.decctx v c d); intros; simpl in *; auto;
  [ econstructor | econstructor 3 | econstructor 3 | econstructor | econstructor 2 | econstructor 3 | econstructor 3
  | econstructor | econstructor 3 | econstructor 3 | econstructor 3 | constructor | econstructor | constructor
  | econstructor 4 | constructor | constructor | econstructor 4 | econstructor | constructor | constructor]; simpl; eauto.
Qed.
Hint Resolve dec_sem_ref.

Lemma dec_ref_sem : forall t c d, MiniML_REF_SEM.dec t c d -> MiniML_Sem.dec t c d.
Proof.
  induction 1 using MiniML_REF_SEM.dec_Ind with
  (P := fun t c d (H : MiniML_REF_SEM.dec t c d) => MiniML_Sem.dec t c d)
  (P0:= fun v c d (H : MiniML_REF_SEM.decctx v c d) => MiniML_Sem.decctx v c d); intros; simpl in *; auto;
  try (constructor; fail);
  try (destruct t; inversion DT; subst; constructor; auto);
  destruct ec; inversion DC; subst; constructor; auto.
Qed.
Hint Resolve dec_ref_sem.

Lemma iter_sem_ref : forall d v, MiniML_Sem.iter d v <-> MiniML_REF_SEM.RS.iter d v.
Proof with eauto with miniml.
destruct d; split; intros H; induction H; subst; simpl in *; auto; try constructor;
inversion_clear D_EM; econstructor 2; simpl in *; eauto; constructor; unfold MiniML_REF_SEM.RS.dec...
Qed.

Lemma eval_sem_ref : forall t v, MiniML_Sem.eval t v <-> MiniML_REF_SEM.RS.eval t v.
Proof with auto.
split; intro H; inversion_clear H; econstructor; inversion_clear D_EM; [ constructor | 
rewrite <- iter_sem_ref | constructor | rewrite iter_sem_ref]; unfold MiniML_REF_SEM.RS.dec in *; eauto.
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
