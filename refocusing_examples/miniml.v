Require Import Util
               Program
               refocusing_semantics.



Module MiniML_PreRefSem <: PRE_REF_SEM.

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

  Coercion val_value := id : val -> value'.


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

  Coercion red_redex := id : red -> redex'.


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


  Instance dead_is_comp : CompPred ckind dead_ckind.
      split. auto. 
  Defined.


  Lemma init_ckind_alive :
      ~dead_ckind init_ckind.
  Proof. auto. Qed.


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


  Lemma death_propagation : 
      forall k ec, dead_ckind k -> dead_ckind (k+>ec).

  Proof. auto. Qed.


  Lemma proper_death : forall k, dead_ckind k -> ~ exists (r : redex k), True.
  Proof. auto. Qed.


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


  Lemma value_trivial1 : forall {k} ec t, 
      forall (v : value k), ~dead_ckind (k+>ec) -> ec:[t] = v ->
          exists (v' : value (k+>ec)), t = v'.

  Proof.
    intros k ec t v H H0.
    destruct ec, v; inversion H0; subst; 
    eauto.
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    destruct v; destruct r; intro H; discriminate H.
  Qed.


  Lemma redex_trivial1 : forall {k} (r : redex k) ec t,
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.
  Proof with auto.
    intros k r ec t H H0.
    destruct ec, r; inversion H0; subst;
    eauto.
  Qed.



  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].

  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.



  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.

  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.
  Notation decomp'   := (@decomp ()).


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM ckind term :=
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End MiniML_PreRefSem.




Module MiniML_Strategy <: REF_STRATEGY MiniML_PreRefSem.

  Import MiniML_PreRefSem.


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

  Proof. auto. Qed.


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

  Proof. auto. Qed.




  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match ec, ec0 with
      | ap_l _,   ap_r _   => immediate_ec ec t /\ immediate_ec ec0 t
      | pair_l _, pair_r _ => immediate_ec ec t /\ immediate_ec ec0 t
      | _, _               => False
      end.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
               (at level 70, t, ec1, ec2 at level 50, no associativity).


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.
  Proof.
    intros k ? ec ec0.
    destruct k, ec, ec0; 
    solve [ autof ].
  Qed.


  Lemma search_order_trans :  forall k t ec0 ec1 ec2, 
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



  Lemma search_order_comp_if : forall t ec0 ec1 k, 
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
          k,t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ec0 = ec1.

  Proof.
    intros t ec0 ec1 k H H0 _ _.

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


  Lemma search_order_comp_fi :
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
          ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof.
    intros k t ec0 ec1 H.

    destruct ec0, ec1; inversion H;
    solve [ intuition ].
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

End MiniML_Strategy.



Module MiniML_RefSem := PreciseRedRefSem MiniML_PreRefSem MiniML_Strategy.




Require Import refocusing_machine.

Module MiniML_EAM := RefEvalApplyMachine MiniML_RefSem.
