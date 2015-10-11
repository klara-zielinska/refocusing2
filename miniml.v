Require Import Util.
Require Import Program.
Require Import refocusing_lang.
Require Import reduction_semantics_facts.


Module MiniML <: RED_LANG.

  Parameter var : Set.


  Inductive expr :=
  | Z   : expr
  | S   : expr -> expr
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr
  | Case: expr -> expr -> var -> expr -> expr
  | Letv: var -> expr -> expr -> expr
  | Fix : var -> expr -> expr
  | Pair: expr -> expr -> expr
  | Fst : expr -> expr
  | Snd : expr -> expr.
  Definition term := expr.
  Hint Unfold term.


  Definition ckind := unit.
  Hint Unfold ckind.


  Inductive val :=
  | vZ    : val
  | vS    : val -> val
  | vLam  : var -> term -> val
  | vVar  : var -> val
  | vPair : val -> val -> val.
  Definition value (_ : ckind) := val.
  Hint Unfold value.
  Notation value' := (value ()).


  Inductive red :=
  | rApp : value' -> value' -> red
  | rLet : var -> value' -> term -> red
  | rFix : var -> term -> red
  | rFst : value' -> red
  | rSnd : value' -> red
  | rCase: value' -> term -> var -> term -> red.
  Definition redex (_ : ckind) := red.
  Hint Unfold redex.
  Notation redex' := (redex ()).


  Inductive ec :=
  | s_c    : ec
  | ap_l   : value' -> ec
  | ap_r   : term -> ec
  | case_c : term -> var -> term -> ec
  | let_c  : var -> term -> ec
  | fst_c  : ec
  | snd_c  : ec
  | pair_l : value' -> ec
  | pair_r : term -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Definition ckind_trans (_ : ckind) (_ : elem_context) : ckind := ().
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


  Definition init_ckind : ckind     := ().
  Definition dead_ckind (_ : ckind) := False.
  Hint Unfold init_ckind dead_ckind.


  Lemma death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).

  Proof.
    intuition.
  Qed.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.
  Notation context' := (context () ()).

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).


  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vZ          => Z
      | vS v        => S (@value_to_term () v)
      | vLam x t    => Lam x t
      | vVar x      => Var x
      | vPair v1 v2 => Pair (@value_to_term () v1) (@value_to_term () v2)
      end.
  Coercion value_to_term : value >-> term.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rApp v1 v2      => App (v1 : term) (v2 : term)
      | rLet x v t      => Letv x (v : term) t
      | rFix x v        => Fix x (v : term)
      | rFst v          => Fst (v : term)
      | rSnd v          => Snd (v : term)
      | rCase v t1 x t2 => Case (v : term) t1 x t2
      end.
  Coercion redex_to_term : redex >-> term.


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof.
    destruct k.

    induction v;
        destruct v';
        inversion 1;

    solve [ f_equal; auto ].
  Qed.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    destruct k.

    destruct r; destruct r'; 
    inversion 1;

    solve [ f_equal; auto using value_to_term_injective ].
  Qed.


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


  Definition elem_plug (t : term) (ec : elem_context) : term :=
      match ec with
      | s_c            => S t
      | ap_l v         => App (v : term) t
      | ap_r t2        => App t t2
      | case_c t1 x t2 => Case t t1 x t2
      | let_c x t2     => Letv x t t2
      | fst_c          => Fst t
      | snd_c          => Snd t
      | pair_l v       => Pair (v : term) t
      | pair_r t2      => Pair t t2
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Lemma elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ec ? ? H.

    destruct ec;
    inversion H;
    solve [ trivial ].
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t.


  Parameter subst : var -> term -> term -> term.


  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rApp (vLam x t) v  => Some (subst x v t)
      | rLet x v t         => Some (subst x v t)
      | rFix x e           => Some (subst x (Fix x e) e)
      | rFst (vPair v1 v2) => Some ((v1 : value') : term)
      | rSnd (vPair v1 v2) => Some ((v2 : value') : term)
      | rCase vZ t _ _     => Some t
      | rCase (vS v) _ x t => Some (subst x (v : value') t)
      | _                  => None
      end.
  Notation contract' := (@contract ()).


  Inductive decomp (k : ckind) : Set :=
  | d_red : forall k', redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.
  Notation decomp' := (decomp ()).


  Definition decomp_to_term {k} (d : decomp k) : term :=
      match d with
      | d_val v => value_to_term v
      | d_red _ r c0 => c0[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition only_empty t k := 
      forall t' {k'} (c : context k k'), c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k).

  Definition only_trivial t k := 
      forall t' {k'} (c : context k k'),  c[t'] = t -> ~ dead_ckind k' -> 
          k = k' /\ c ~= [.](k) \/ exists (v : value k'), t' = v.


  Lemma value_trivial : forall {k} (v : value k), only_trivial v k.

  Proof with auto.
    intros k1 v t k2 c; revert t.

    induction c; intros t H _.
    - intuition.
    - right.
      simpl in H.
      destruct (IHc _ H) as [(H1, H2) | (v0, H1)]...
      + dep_subst.
        simpl in H.
        destruct ec0, k2, v; 
            inversion H; 
        solve [ eexists; eauto ].
      + destruct ec0, k2, v0;
            inversion H1; 
        solve [ eexists; eauto ].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    destruct v; destruct r; intro H; discriminate H.
  Qed.


  Lemma ot_subterm_val : 
      forall t t0 ec k, only_trivial t k -> ec:[t0] = t -> 
          exists v : value k, t0 = v.

  Proof with auto.
    intros.
    destruct (H t0 _ (ec0 =: [.])) as [(H1, H2) | (v, H1)]...
    - discriminateJM H2.
    - exists v; destruct k...
  Qed.


  Ltac ot_v t ec v0 H0 :=
      match goal with H : only_trivial ?t0 _ |- _ => unify t0 (ec:[t]);
          destruct (ot_subterm_val _ t ec _ H) as (v0, H0); [auto | subst t]
      end.

  Tactic Notation "ot_v" constr(t) constr(ec) "as" ident(v0) ident(H0) := 
      ot_v t ec v0 H0.

  Ltac mlr rv :=
      match goal with |- (exists v : value ?k, _ = value_to_term v) \/
                         (exists r : redex ?k, _ = redex_to_term r)      =>
          destruct k;
          match type of rv with
          | value ?k0 => destruct k0; left;  exists rv
          | redex ?k0 => destruct k0; right; exists rv
          end; 
          simpl; auto
      end.



  Lemma trivial_val_red : 
      forall k t, only_trivial t k ->
          (exists (v : value k), t = v) \/ (exists (r : redex k), t = r).

  Proof with auto.
    intros; destruct t.
    - mlr (vZ : value').
    - ot_v t s_c as v H0.
      mlr (vS v : value').
    - destruct k.
      ot_v t1 (ap_r t2) as v1 H1.
      ot_v t2 (ap_l v1) as v2 H2.
      mlr (rApp v1 v2 : redex').
    - mlr (vVar v : value').
    - mlr (vLam v t : value').
    - ot_v t1 (case_c t2 v t3) as v1 H1.
      mlr (rCase v1 t2 v t3 : redex').
    - ot_v t1 (let_c v t2) as v1 H1.
      mlr (rLet v v1 t2 : redex').
    - mlr (rFix v t : redex').
    - destruct k.
      ot_v t1 (pair_r t2) as v1 H1.
      ot_v t2 (pair_l v1) as v2 H2.
      mlr (vPair v1 v2 : value').
    - ot_v t fst_c as v H0.
      mlr (rFst v : redex').
    - ot_v t snd_c as v H0.
      mlr (rSnd v : redex').
  Qed.


  Lemma dead_context_dead : 
      forall {k1 k2}, context k1 k2 -> dead_ckind k1 -> dead_ckind k2.

  Proof with auto.
    intros ? ? c H; revert c.
    induction 1.
    - trivial.
    - apply death_propagation...
  Qed.


  Lemma proper_death : forall k, dead_ckind k -> 
                           ~ exists k' (c : context k k') (r : redex k'), True.

  Proof with auto.
    intros k H; destruct k...
  Qed.

End MiniML.




Module MiniML_Ref <: RED_REF_LANG.

  Module R  := MiniML.
  Module RF := RED_LANG_Facts R.
  Export R.
  Import RF.


  Module DEC <: REF_STEP R.

    Inductive interm_dec k : Set :=
    | in_red  : redex k -> interm_dec k
    | in_term : term -> elem_context -> interm_dec k
    | in_val  : value k -> interm_dec k
    | in_dead : interm_dec k.
    Arguments in_red {k} _.    Arguments in_val {k} _.
    Arguments in_term {k} _ _. Arguments in_dead {k}.

    Definition dec_term (t : term) k : interm_dec k :=
        match t with
        | Z              =>  in_val vZ
        | S t            =>  in_term t s_c
        | App t1 t2      =>  in_term t1 (ap_r t2)
        | Var x          =>  in_val (vVar x)
        | Lam x t        =>  in_val (vLam x t)
        | Case t ez x es =>  in_term t (case_c ez x es)
        | Letv x t e     =>  in_term t (let_c x e)
        | Fix x t        =>  in_red (rFix x t)
        | Pair t1 t2     =>  in_term t1 (pair_r t2)
        | Fst t          =>  in_term t fst_c
        | Snd t          =>  in_term t snd_c
        end.

    Definition dec_context (ec : elem_context) k (v : value (k+>ec)) : interm_dec k :=
        match ec with
        | s_c             =>  in_val (vS v)
        | ap_l v0         =>  in_red (rApp v0 v)
        | ap_r t          =>  in_term t (ap_l v)
        | case_c ez x es  =>  in_red (rCase v ez x es)
        | let_c x e       =>  in_red (rLet x v e)
        | fst_c           =>  in_red (rFst v)
        | snd_c           =>  in_red (rSnd v)
        | pair_l v0       =>  in_val (vPair v0 v)
        | pair_r t        =>  in_term t (pair_l v)
        end.


    Lemma dec_term_correct : 
        forall (t : term) k, match dec_term t k with
        | in_red r      => t = r
        | in_val v      => t = v
        | in_term t' ec => t = ec:[t']
        | in_dead       => dead_ckind k 
        end.

    Proof with auto.
      destruct k, t; simpl... 
    Qed.


    Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
    Proof.
      intros ? k H.
      inversion H.
    Qed.


    Lemma dec_term_next_alive : 
        forall t k t0 ec0, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      auto.
    Qed.


    Lemma dec_context_correct : 
        forall ec k v, match dec_context ec k v with
        | in_red r      => ec:[v] = r
        | in_val v'     => ec:[v] = v'
        | in_term t ec' => ec:[v] = ec':[t]
        | in_dead       => dead_ckind (k+>ec)
        end.

    Proof.
      intros ec k v.
      destruct k, ec; dependent destruction v;
      simpl;
      solve [ auto ].
    Qed.


    Lemma dec_context_from_dead : forall ec k v, 
        dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

    Proof.
      intros ec k v H.
      inversion H.
    Qed.


    Lemma dec_context_next_alive : forall ec k v {t ec0}, 
        dec_context ec k v = in_term t ec0 -> ~ dead_ckind (k+>ec0).

    Proof.
      auto.
    Qed.

  End DEC.

  Export DEC.


  Lemma redex_trivial : forall {k} (r : redex k), only_trivial r k.
  Proof with auto.
    intros k1 v t k2 c; revert t.

    induction c; intros t H _.
    - intuition.
    - right.
      simpl in H.
      destruct (IHc _ H) as [(H1, H2) | (v0, H1)]...
      + dep_subst.
        simpl in H.
        destruct ec0, k2, v; 
            inversion H; 
        solve [ eexists; eauto ].
      + destruct ec0, k2, v0;
            inversion H1; 
        solve [ eexists; eauto ].
  Qed.


  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec, t = ec:[t0] -> subterm_one_step t0 t.


  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    RED_REF_LANG_Help.prove_st_wf.
  Qed.


  Definition subterm_order := clos_trans_1n term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40, no associativity).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_l _ _ wf_st1.


  Definition ec_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match ec, ec0 with
      | ap_l _,   ap_r _   => immediate_ec ec t /\ immediate_ec ec0 t
      | pair_l _, pair_r _ => immediate_ec ec t /\ immediate_ec ec0 t
      | _, _               => False
      end.
  Notation "k , t |~  ec1 << ec2 " := (ec_order k t ec1 ec2) (at level 40, no associativity).


  Lemma wf_eco : forall k t, well_founded (ec_order k t).
  Proof.
    RED_REF_LANG_Help.prove_ec_wf.
  Qed.


  Lemma ec_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.
  Proof.
    intros k ? ec ec0.
    destruct k, ec, ec0; 
    solve [ autof ].
  Qed.


  Lemma ec_order_trans :  forall k t ec0 ec1 ec2, 
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 -> 
      k,t |~ ec0 << ec2.

  Proof.
    intros k ? ec0 ec1 ec2 ? ?.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.



  Ltac inj_vr := match goal with
  | [Hv : value_to_term _ = value_to_term _ |- _] => apply value_to_term_injective in Hv
  | [Hr : redex_to_term _ = redex_to_term _ |- _] => apply redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.



  Lemma ec_order_comp_if : forall t ec0 ec1, 
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      forall k, ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k,t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ec0 = ec1.

  Proof.
    intros t ec0 ec1 H H0 k _ _.

    assert (G := H); assert (G0 := H0).
    destruct H as (t0, H), H0 as (t1, H0).
    rewrite <- H in H0. 

    destruct ec0, ec1; inversion H0;

    solve
    [ auto 
    | inj_vr; subst; 
      simpl;
      intuition constructor ]. 
  Qed.


  Lemma ec_order_comp_fi :
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
          ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof.
    intros k t ec0 ec1 H.

    destruct ec0, ec1; inversion H;
    solve [ intuition ].
  Qed.


  Lemma dec_term_red_empty : 
      forall t {k} (r : redex k), dec_term t k = in_red r -> only_empty t k.

  Proof with auto.
    intros t k r H.

    destruct t;
        inversion H.

    clear r H H1.

    intros t0 k' c; generalize dependent t0.
    induction c;
        intros; simpl in *.
    - intuition.
    - destruct (IHc _ H) as (H1, H2)...
      dep_subst.
      destruct ec0; inversion H.
  Qed.


  Lemma dec_term_val_empty : 
      forall t {k} (v : value k), dec_term t k = in_val v -> only_empty t k.

  Proof.
    intros t k v H.

    destruct t;
        inversion H;

    solve 
    [
        clear v H H1;

        intros t0 k' c; generalize dependent t0;
        induction c;
            intros; simpl in *;
        solve
        [ intuition
        | destruct (IHc _ H) as (H1, H2); auto;
          dep_subst;
          destruct ec0; inversion H ]
    ].
  Qed.


  Lemma dec_term_term_top : forall t k {t' ec}, 
            dec_term t k = in_term t' ec -> forall ec', ~ k, t |~ ec << ec'.

  Proof.
    intros t t' k ec H ec' H0.
    destruct t; 
        inversion H; subst;
        destruct ec';
    solve [ inversion H0 ].
  Qed.


  Lemma dec_context_red_bot : 
      forall k ec v r, dec_context ec k v = in_red r -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.

  Proof.
    intros k ec v r H ec' H0.
    destruct ec, ec';
    solve [ inversion H; inversion H0 ].
  Qed.


  Lemma dec_context_val_bot : 
      forall k ec v v', dec_context ec k v = in_val v' -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k ec v v' H ec' H0.
    destruct ec, ec'; 
    solve [ inversion H; inversion H0 ].
  Qed.


  Lemma dec_context_term_next : 
      forall ec0 k v t ec1, dec_context ec0 k v = in_term t ec1 ->
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.

  Proof.
    intros ec0 k v t ec1 H.

    assert (H0 := dec_context_correct ec0 k v); rewrite H in H0.

    destruct ec0; 
        inversion H; subst;

    solve [
        split;
        [ constructor; 
          eexists; eauto
        | intros ec'' H1 H2; 
          destruct ec''; 
          inversion H1; inversion H2
    ]   ].
  Qed.


  Lemma elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.
  Proof.
    intros t ec t' H k ec' H0.

    destruct ec, ec'; 
        inversion H0; subst;

    solve
    [ destruct H1 as (t1, H1);
      inversion H1;
      eexists; trivial ].
  Qed.

End MiniML_Ref.




Require Import refocusing_semantics_derivation.
Require Import refocusing_machine.

Module MiniML_REF_SEM := RedRefSem MiniML_Ref.
Module MiniML_EAM     := ProperEAMachine MiniML MiniML_REF_SEM.
