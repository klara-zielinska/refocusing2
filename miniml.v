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


  Definition ckind_trans (_ : ckind) (_ : elem_context) : ckind := tt.
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




Module MiniMLRef <: RED_REF_LANG.

  Module R  := MiniML.
  Module RF := RED_LANG_Facts R.
  Import R.
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

End MiniMLRef.




Require Import refocusing_semantics_derivation.
Require Import refocusing_machine.

Module MiniML_REF_SEM := RedRefSem MiniMLRef.
Module MiniML_EAM     := ProperEAMachine MiniML MiniML_REF_SEM.




Module MiniML_HandSem <: RED_SEM MiniML.

  Module RF := RED_LANG_Facts MiniML.
  Import MiniML.
  Import RF.


  Lemma decompose : forall (t : term) k1, ~ dead_ckind k1 ->
      (exists (v : value k1), t = v) \/
      (exists k2 (r : redex k2) (c : context k1 k2), t = c[r]).

  Proof with simpl; f_equal; eauto.
    intros t () _.

    induction t.

    - left.
      exists vZ...

    - destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + left.
        exists (vS v)...
      + right.
        exists () r (c ~+ s_c =: [.](())).
        rewrite plug_compose...

    - right; exists ().
      destruct IHt1 as [(v1, ?) | ((), (r1, (c1, ?)))].
      + destruct IHt2 as [(v2, ?) | ((), (r2, (c2, ?)))].
        * exists (rApp v1 v2) [.](())...
        * exists r2 (c2 ~+ ap_l v1 =: [.](())).
          rewrite plug_compose...
      + exists r1 (c1 ~+ ap_r t2 =: [.](())).
        rewrite plug_compose...

    - left.
      eexists (vVar _)...

    - left.
      eexists (vLam _ _)...

    - right.
      destruct IHt1 as [(v1, ?) | ((), (r, (c, ?)))].
      + eexists (), (rCase v1 _ _ _), [.]...
      + eexists (), r, (c ~+  case_c _ _ _ =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt1 as [(v1, ?) | ((), (r, (c, ?)))].
      + eexists (), (rLet _ _ _), [.]...
      + eexists (), r, (c ~+ let_c _ _ =: [.]).
        rewrite plug_compose...

    - right.
      eexists (), (rFix _ _), [.]...

    - destruct IHt1 as [(v1, ?) | ((), (r1, (c1, ?)))].
      + destruct IHt2 as [(v2, ?) | ((), (r2, (c2, ?)))].
        * left.
          exists (vPair v1 v2)...
        * right.
          eexists (), r2, (c2 ~+ pair_l v1 =: [.]).
          rewrite plug_compose...
      + right.
        eexists (), r1, (c1 ~+ pair_r t2 =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + eexists (), (rFst v), [.]... 
      + eexists (), r, (c ~+ fst_c =: [.]).
        rewrite plug_compose...

    - right.
      destruct IHt as [(v, ?) | ((), (r, (c, ?)))].
      + eexists (), (rSnd v), [.]... 
      + eexists (), r, (c ~+ snd_c =: [.]).
        rewrite plug_compose...
  Qed.



  Inductive __dec : term -> context' -> decomp' -> Prop :=

  | d_z   : forall c d, decctx vZ c d               -> __dec Z c d

  | d_s   : forall t c d, __dec t (s_c =: c) d      -> __dec (S t) c d

  | d_case: forall t ez x es c d, 
              __dec t (case_c ez x es =: c) d       -> __dec (Case t ez x es) c d

  | d_var : forall x c d, decctx (vVar x) c d       -> __dec (Var x) c d

  | d_lam : forall x t c d, decctx (vLam x t) c d   -> __dec (Lam x t) c d

  | d_app : forall t1 t2 c d, 
              __dec t1 (ap_r t2 =: c) d             -> __dec (App t1 t2) c d

  | d_let : forall x t e c d, 
              __dec t (let_c x e =: c) d            -> __dec (Letv x t e) c d

  | d_fix : forall x t c, 
              __dec (Fix x t) c (d_red (rFix x t) c)

  | d_pair: forall t1 t2 c d, 
              __dec t1 (pair_r t2 =: c) d           -> __dec (Pair t1 t2) c d

  | d_fst : forall t c d, __dec t (fst_c =: c) d    -> __dec (Fst t) c d

  | d_snd : forall t c d, __dec t (snd_c =: c) d    -> __dec (Snd t) c d


  with decctx : value' -> context' -> decomp' -> Prop :=

  | dc_em : forall v,
              decctx v [.] (d_val v)

  | dc_s  : forall v c d, decctx (vS v) c d         -> decctx v (s_c =: c) d

  | dc_cs : forall v x ez es (c : context'),
              decctx v (case_c ez x es =: c) (d_red (rCase v ez x es) c)

  | dc_apr: forall v t (c : context') d, 
              __dec t (ap_l v =: c) d -> decctx v (ap_r t =: c) d

  | dc_apl: forall v v0 (c : context'),
              decctx v (ap_l v0 =: c) (d_red (rApp v0 v) c)

  | dc_let: forall v x e (c : context'),
              decctx v (let_c x e =: c) (d_red (rLet x v e) c)

  | dc_p_r: forall t v (c : context') d, 
              __dec t (pair_l v =: c) d             -> decctx v (pair_r t =: c) d

  | dc_p_l: forall v v0 c d, 
              decctx (vPair v0 v) c d               -> decctx v (pair_l v0 =: c) d

  | dc_fst: forall v (c : context'), 
              decctx v (fst_c =: c) (d_red (rFst v) c)

  | dc_snd: forall v (c : context'),
              decctx v (snd_c =: c) (d_red (rSnd v) c).

  Definition destruct_ckind : forall {P : ckind -> Type}, P () -> forall k, P k :=
      fun P H k => match k as k' return P k' with () => H end.
  Notation "# t" := (destruct_ckind t) (at level 0).


  Definition dec t : forall {k1 k2 : ckind}, context k1 k2 -> decomp k1 -> Prop := 
      ##(__dec t).

  Definition decctx' : 
      forall {k2}, value k2 -> forall {k1}, context k1 k2 -> decomp k1 -> Prop :=
      #(fun v => #(decctx v)).

  Scheme dec_Ind    := Induction for __dec  Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Lemma dec_val_self : forall (v : value') c d, __dec v c d <-> decctx v c d.
  Proof.
    induction v;
        intros c d; split; intro H;
        inversion H; dep_subst; 

    solve
    [ auto

    | constructor; auto

    | match goal with H : _ |- _ => 
      apply IHv in H;
      inversion H1; dep_subst;
      solve [ auto ]
      end

    | match goal with H : _ |- _ => 
      apply IHv1 in H;
      inversion H; dep_subst;
      match goal with H : _ |- _ => 
      apply IHv2 in H;
      inversion H; dep_subst;
      solve [ auto ]
      end end

    | constructor; fold (@value_to_term ()); 
      apply IHv; 
      constructor;
      auto

    | constructor; fold (@value_to_term ());
      apply IHv1; constructor;
      apply IHv2; constructor;
      auto ].
  Qed.



  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> c[t] = d.
  Proof with auto.
    destruct k1, k2.
    induction 1 using dec_Ind with
    (P  := fun t c d (_ : __dec t c d)  => c[t] = d)
    (P0 := fun v c d (_ : decctx v c d) => c[v] = d)...
  Qed.


  Lemma dec_plug :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec c[t] c0 d -> dec t (c ~+ c0) d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t0 d H H0.
      destruct ec0;
          assert (hh := IHc _ _ _ _ (death_propagation2 _ _ H) H0);
          destruct k1, k2, k3; simpl in hh;
          dependent destruction hh; subst;
      solve
      [ auto
      | apply dec_val_self in hh;
        inversion hh; dep_subst;
        auto ].
  Qed.


  Lemma dec_plug_rev :
      forall {k1 k2} (c : context k1 k2) {k3} {c0 : context k3 k1} {t d}, 
          ~ dead_ckind k2 -> dec t (c ~+ c0) d -> dec c[t] c0 d.
  Proof.
    induction c.
    - auto.
    - intros k3 c0 t d H H0.
      simpl.
      apply IHc; eauto using death_propagation2.
      destruct ec0, k1, k2, k3;
      solve 
      [ constructor; 
        auto
      | constructor;
        apply dec_val_self;
        constructor;
        assumption ].
  Qed.


  Lemma dec_redex_self : forall {k2} (r : redex k2) {k1} (c : context k1 k2), 
                             dec (redex_to_term r) c (d_red r c).
  Proof.
    destruct k2, k1.
    destruct r as [v1 v2 | x v t | x t | v | v | v t1 x t2];
        intro c;
    solve 
    [ constructor;
      repeat (apply dec_val_self; constructor); 
      auto ].
  Qed.


  Lemma dec_value_self : forall {k} (v : value k), 
                             ~ dead_ckind k -> dec v [.] (d_val v).
  Proof with auto.
    intros k v H.
    destruct k.
    apply dec_val_self.
    constructor...
  Qed.


  Inductive decempty : term -> forall {k}, decomp k -> Prop :=
  | d_intro : forall {t k} {d : decomp k}, dec t [.] d -> decempty t d.

  Inductive iter : forall {k}, decomp k -> value k -> Prop :=
  | i_val : forall {k} (v : value k), iter (d_val v) v
  | i_red : forall {k2} (r : redex k2) {t k1} (c : context k1 k2) {d v},
                contract r = Some t -> decempty c[t] d -> iter d v ->
                iter (d_red r c) v.

  Inductive eval : term -> value init_ckind -> Prop :=
  | e_intro : forall {t} {d : decomp init_ckind} {v : value init_ckind}, 
                  decempty t d -> iter d v -> eval t v.

End MiniML_HandSem.



(*
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