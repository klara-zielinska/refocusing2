Require Import List
               Util
               refocusing_semantics.


(*** Local library ***)


(* Positive nat: *)

Inductive pnat : Set := POne | PS : pnat -> pnat.
Fixpoint pnat2nat n := match n with POne => 1 | PS n => S (pnat2nat n) end.
Coercion pnat2nat : pnat >-> nat.

Lemma pnat2nat_injective : forall m n, pnat2nat m = pnat2nat n -> m = n.
Proof.
  induction m; 
      intros n H; 
      destruct n; inversion H; subst.
  - auto.
  - destruct n; discriminate.
  - destruct m; discriminate.
  - f_equal; auto.
Qed.


(* Non-empty lists: *)

Inductive plist (T : Type) : Type := 
| PSingle : T -> plist T
| PCons   : T -> plist T -> plist T.
Arguments PSingle {T} _. Arguments PCons {T} _ _.

Fixpoint plist2list {T} (l : plist T) :=
    match l with
    | PSingle e => (e::nil) %list
    | PCons e l => (e::plist2list l) %list
    end.
Coercion plist2list : plist >-> list.

Fixpoint pcons2 {T} (e : T) (l : list T) := 
    match l with 
    | nil => PSingle e 
    | cons e' l => PCons e (pcons2 e' l) end.

Lemma plist2list_injective :                                forall {T} (l1 l2 : plist T),
    (l1 : list T) = (l2 : list T) -> l1 = l2.

Proof.
  intro T.
  induction l1;
      intros l2 H;
      destruct l2; inversion H; subst.
  - auto.
  - destruct l2; discriminate.
  - destruct l1; discriminate.
  - f_equal; auto.
Qed.

Lemma pcons2_injective :                         forall {T} (e1 e2 : T) (l1 l2 : list T),
    pcons2 e1 l1 = pcons2 e2 l2 -> e1 = e2 /\ l1 = l2.

Proof.
  intros T e1 e2 l1; revert e1 e2.
  induction l1; intros e1 e2 l2 H;
  destruct l2; inversion H; subst.
  - auto.
  - destruct (IHl1 a t l2 H2); subst; auto.
Qed.

Lemma pcons2_and_pcons :                                forall {T} (e : T) (l : plist T),
    PCons e l = pcons2 e l.

Proof. 
  intros T e l; revert e.
  induction l; intro e;
  simpl; 
  solve [f_equal; eauto].
Qed.

(*** Local library end ***)







Module Lam_KES_CBN_PreRefSem <: PRE_PRECISE_REF_SEM.


  Inductive term0 : Set :=
  | Lam0: pnat  -> term0 -> term0
  | App0: term0 -> term0 -> term0
  | Var0: nat   -> nat   -> term0.


  Inductive closure : Set :=
  | Cl : term0 -> plist (list closure) -> closure.

  Notation thunk := (list closure).
  Notation env   := (plist thunk).


  Inductive term' : Set :=
  | Cl_t  : closure          -> term'
  | App   : term' -> closure -> term'.
  Coercion Cl_t : closure >-> term'.
  Definition term := term'.
  Hint Unfold term.


  Definition elem_context := closure.
  Hint Unfold elem_context.

  Definition elem_plug (t : term) (ec : elem_context) : term := App t ec.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Definition ckind : Set := unit.
  Hint Unfold ckind.

  Definition ckind_trans (k : ckind) (ec : elem_context) : ckind := tt.
  Infix "+>" := ckind_trans (at level 50, left associativity).


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix    "=:"       := ccons (at level 60, right associativity).


  Fixpoint compose {k1 k2} (c0 : context k1 k2) 
                      {k3} (c1 : context k3 k1) : context k3 k2 := 
      match c0 in context _ k2' return context k3 k2' with
      | [.]     => c1
      | ec=:c0' => ec =: compose c0' c1
      end.
  Infix "~+" := compose (at level 60, right associativity).


  Fixpoint plug (t : term) {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t.


  Inductive value' : Set := 
  | vLam_cl : pnat -> term0 -> env -> value'.
  Definition value (_: ckind) := value'.

  Definition value_to_term {k} (v : value k) : term :=
      match v with vLam_cl n t e => Cl (Lam0 n t) e end.
  Coercion  value_to_term : value >-> term.


  Inductive redex' : Set :=
  | rBeta   : pnat -> term0 -> thunk -> list thunk -> closure -> redex'
  | rSubApp : term0 -> term0 -> env -> redex'
  | rSubVar : nat -> nat -> env -> redex'.
  Definition redex (_: ckind) := redex'.

  Definition redex_to_term {k} (r : redex k) : term :=
      match r with 
      | rBeta n t th e cl  => App (Cl (Lam0 n t) (pcons2 th e)) cl 
      | rSubApp t1 t2 e    => Cl (App0 t1 t2) e
      | rSubVar p o e      => Cl (Var0 p o) e
      end.
  Coercion redex_to_term : redex >-> term.


  Definition init_ckind : ckind     := tt.
  Definition dead_ckind (_ : ckind) := False.

  Instance dead_is_comp : CompPred _ dead_ckind.
      split. auto.
  Defined.


  Definition contract {k} (r : redex k) : option term :=
      match r with
      | rBeta POne   t th e cl => Some (Cl t (PCons nil (pcons2 (cl::th) e)) : term)
      | rBeta (PS n) t th e cl => Some (Cl (Lam0 n t) (pcons2 (cl::th) e) : term)
      | rSubApp t1 t2 e        => Some (App (Cl t1 e) (Cl t2 e))
      | rSubVar p o e          => match nth_error e (S p) with 
                                  | None    => None
                                  | Some th => option_map Cl_t (nth_error th o)
                                  end
      end.


  Inductive decomp k : Set :=
  | d_red : forall {k'}, redex k' -> context k k' -> decomp k
  | d_val : value k -> decomp k.
  Arguments d_val {k} _. Arguments d_red {k} {k'} _ _.


  Definition decomp_to_term {k} (d : decomp k) :=
      match d with
      | d_val v     => value_to_term v
      | d_red _ r c => c[r]
      end.
  Coercion decomp_to_term : decomp >-> term.


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


  Definition reduce k t1 t2 := 
      exists {k'} (c : context k k') (r : redex k') t,  dec t1 k (d_red r c) /\
          contract r = Some t /\ t2 = c[t].


  Instance lrws : LABELED_REWRITING_SYSTEM ckind term := 
  { ltransition := reduce }. 
  Instance rws : REWRITING_SYSTEM term := 
  { transition := reduce init_ckind }.


  Definition immediate_subterm t0 t := 
      exists ec, t = ec:[t0].


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2)           (at level 70, no associativity).



  Lemma init_ckind_alive :
      ~dead_ckind init_ckind.

  Proof. auto. Qed.


  Lemma elem_plug_injective1 :                                           forall ec t0 t1,
      ec:[t0] = ec:[t1] -> t0 = t1.

  Proof. 
    intros ec t0 t1 H.
    destruct ec; inversion H; 
    auto.
  Qed.


  Lemma value_to_term_injective :                            forall {k} (v v' : value k),
      value_to_term v = value_to_term v' -> v = v'.

  Proof.
    intros k v v' H.
    destruct v, v'; inversion H; subst.
    f_equal.
  Qed.


  Lemma redex_to_term_injective :                            forall {k} (r r' : redex k),
      redex_to_term r = redex_to_term r' -> r = r'.

  Proof.
    intros k r r' H.
    destruct r, r'; inversion H; subst; 
    try solve [ f_equal;
                eauto using plist2list_injective ].
    - destruct (pcons2_injective _ _ _ _ H3); subst; auto.
  Qed.


  Lemma death_propagation :                                                  forall k ec,
      dead_ckind k -> dead_ckind (k+>ec).

  Proof. auto. Qed.


  Lemma proper_death :                                                          forall k,
      dead_ckind k -> ~ exists (r : redex k), True.

  Proof. auto. Qed.


  Lemma value_trivial1 :                                 forall {k} ec {t} (v : value k),
      ~dead_ckind (k+>ec) -> ec:[t] = v -> 
          exists (v' : value (k+>ec)), t = v'.

  Proof. 
    intros k ec t v H H0. 
    destruct ec, v; 
    discriminate.
  Qed.


  Lemma value_redex :                             forall {k} (v : value k) (r : redex k),
      value_to_term v <> redex_to_term r.

  Proof. 
    intros k v r. 
    destruct v, r; 
    solve [eauto].
  Qed.


  Lemma redex_trivial1 :                                   forall {k} (r : redex k) ec t,
      ~dead_ckind (k+>ec) -> ec:[t] = r -> 
          exists (v : value (k+>ec)), t = v.

  Proof. 
    intros k r ec t H H0. 
    destruct ec, r; inversion H0; subst.
    - eexists (vLam_cl _ _ _); reflexivity.
  Qed.


  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition wf_subterm_order : well_founded subterm_order
      := wf_clos_trans_l _ _ wf_immediate_subterm.



  (* Extras *)
  Fixpoint closed_within (t : term0) (el : plist nat) : Prop :=
      match t with
      | Lam0 n t   => match el with 
                      | PSingle m  => closed_within t (PCons 0 (PSingle (n + m)))
                      | PCons m el => closed_within t (PCons 0 (PCons (n + m) el))
                      end
      | App0 t1 t2 => closed_within t1 el /\ closed_within t2 el
      | Var0 p o   => match List.nth_error el (S p) with
                      | None   => False
                      | Some n => o < n
                      end
      end.


  Fixpoint env_layout (e : env) : plist nat := 
      match e with
      | PSingle th => PSingle (length th)
      | PCons th e => PCons (length th) (env_layout e)
      end.


  (* To think: change the Inductive to a Fixpoint *)
  Inductive closed_cl : closure -> Prop :=
  | cc : forall t (e : env), closed_within t (env_layout e) -> closed_env e -> 
                                                                       closed_cl (Cl t e)

  with closed_env : env -> Prop :=
  | ce1 : forall th, closed_th th                   -> closed_env (PSingle th)
  | ce2 : forall th e, closed_th th -> closed_env e -> closed_env (PCons th e)

  with closed_th : thunk -> Prop :=
  | ct1 : closed_th nil
  | ct2 : forall cl th, closed_cl cl -> closed_th th -> closed_th (cl :: th).

  Scheme cc_Ind := Induction for closed_cl  Sort Prop
    with ce_Ind := Induction for closed_env Sort Prop
    with ct_Ind := Induction for closed_th  Sort Prop.


  Fixpoint closed (t : term) : Prop := 
      match t with 
      | Cl_t cl  => closed_cl cl
      | App t cl => closed t /\ closed_cl cl
      end.


  Lemma env_thunks_closed :                                                forall e n th,
      closed_env e -> nth_error e n = Some th -> closed_th th.

  Proof with auto.
    intros e n th H; revert n th.
    induction H; intros n th' H1.
    - destruct n as [ | [ | ?]];
      simpl in H1; unfold Specif.value in H1; inversion H1; subst...
    - destruct n as [ | n].
      + simpl in H1; unfold Specif.value in H1; inversion H1; subst...
      + simpl in H1; eauto.
  Qed.


  Lemma thunk_closures_closed :                                           forall th n cl,
      closed_th th -> nth_error th n = Some cl -> closed_cl cl.

  Proof.
    intros th n cl H; revert n cl.
    induction H; 
        intros n cl' H1;
        destruct n;
        inversion H1; subst;
    solve [eauto].
  Qed.


  Lemma env_layout_nth_is_th_size :                              forall (e : env) n th m,
      nth_error e n = Some th -> nth_error (env_layout e) n = Some m -> 
          m = length th.

  Proof.
    intros e n; revert e.
    induction n as [ | n];
        intros e th m H H0;
        destruct e as [th1 | th1 e]; inversion H; subst;
    solve 
    [ inversion H0;
      auto
    | destruct n; discriminate
    | eauto ].
  Qed. 


  Lemma env_layout_semi_correct :                                     forall (e : env) n,
      nth_error e n = None <-> nth_error (env_layout e) n = None.

  Proof.
    intros e n; revert e.
    induction n as [ | n]; 
        intros e; split; intro H;
        destruct e; inversion H; subst; 
    solve
    [ auto
    | destruct n; auto
    | apply IHn; auto ].
  Qed. 


  Require Import Arith.

  Lemma nth_error_safe :                                       forall {T} (l : list T) n,
      n < List.length l -> exists e, nth_error l n = Some e.

  Proof.
    intros T l n; revert l.
    induction n; intros l H.
    - destruct l.
      + contradict H; auto with arith.
      + exists t; auto.
    - destruct l.
      + contradict H; auto with arith.
      + assert (n < length l).
        { auto with arith. }
        eauto.
  Qed.



  Lemma contract_closed :                                       forall {k} (r : redex k),
      closed r -> exists t, contract r = Some t /\ closed t.

  Let Ar : forall m n, S (m + n) = m + S n. 
  Proof. auto with arith. Qed.

  Proof with eauto.
    intros k r H.
    destruct r; simpl in H.

    - destruct p as [ | n];
      [ exists (Cl t (PCons nil (pcons2 (c::l) l0)))
      | exists (Cl (Lam0 n t) (pcons2 (c::l) l0))];
      simpl; intuition;
          inversion H0; subst;
          destruct l0; simpl in H3;
          try rewrite Ar in H3;
          inversion H4; subst;
      solve [repeat (constructor; auto)].

    - eexists. intuition. 
      inversion H; subst.
      simpl in *.
      split; 
      solve [constructor; intuition].

    - inversion H; subst.
      cut (exists th, nth_error p (S n) = Some th /\ 
           exists cl, nth_error th n0 = Some cl).
      {
          intros [th [H0 [cl H1]]].
          exists cl.
          unfold contract.
          rewrite H0.
          rewrite H1.
          intuition.
          eapply thunk_closures_closed...
          eauto using env_thunks_closed.
      }

      unfold closed_within in H2.
      remember (nth_error (env_layout p) (S n)) as th_size_o; 
      destruct th_size_o as [n1 | ]; autof.
      remember (nth_error p (S n)) as th_o; 
      destruct th_o as [th | ];
          symmetry in Heqth_size_o, Heqth_o.
      + assert (n1 = length th). 
        { eauto using env_layout_nth_is_th_size. }
        exists th.
        intuition.
        subst.
        destruct (nth_error_safe th n0) as [cl H1]; auto.
        solve [eauto].
      + apply env_layout_semi_correct in Heqth_o.
        congruence.
  Qed.


  Lemma context_closed :                            forall {k1 k2} (c : context k1 k2) t,
      closed c[t] -> closed t.

  Proof.
    induction c; intros t H.
    - auto.
    - assert (closed ec:[t]); auto.
      destruct ec; inversion H0; subst.
      auto.
  Qed.


  Lemma plug_replace_closed :                   forall {k1 k2} (c : context k1 k2) t1 t2,
      closed c[t1] -> closed t2 -> closed c[t2].

  Proof.
    induction c; intros t1 t2 H H0.
    - auto.
    - apply (IHc ec:[t1]); auto. 
      simpl in H.
      apply context_closed in H; simpl in H.
      simpl.
      intuition.
  Qed.


  Lemma red_step_closed :              forall {k1 k2} (c : context k1 k2) (r : redex k2),
      closed c[r] -> exists t, contract r = Some t /\ closed c[t].

  Proof.
    intros ? ? ? r ?.
    destruct (contract_closed r) as [t [H0 H1]].
    { eauto using context_closed. }
    exists t.
    eauto using plug_replace_closed.
  Qed.


  Class SafeKRegion (k : ckind) (P : term -> Prop) :=
  { 
      preservation :                                                        forall t1 t2,
          P t1  ->  k |~ t1 → t2  ->  P t2;
      progress :                                                               forall t1,
          P t1  ->  (exists (v : value k), t1 = v) \/ (exists t2, k |~ t1 → t2)
  }.

End Lam_KES_CBN_PreRefSem.




Module Lam_KES_CBN_Strategy <: REF_STRATEGY Lam_KES_CBN_PreRefSem.

  Import Lam_KES_CBN_PreRefSem.


  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_dead : interm_dec k.
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k} _ _. Arguments in_dead {k}.


  Definition dec_term (t : term) (k : ckind) : interm_dec k :=
      match t with
      | Cl_t (Cl (Lam0 n t) e)   => in_val (vLam_cl n t e)
      | Cl_t (Cl (App0 t1 t2) e) => in_red (rSubApp t1 t2 e)
      | Cl_t (Cl (Var0 p o) e)   => in_red (rSubVar p o e)
      | App t cl                 => in_term t cl
      end.


  Definition dec_context (ec : elem_context) (k : ckind) (v : value (k+>ec)) 
                 : interm_dec k :=

      match v with
      | vLam_cl n t e => match e with 
                         | PSingle th => in_red (rBeta n t th nil ec)
                         | PCons th e => in_red (rBeta n t th e ec)
                         end
      end.


  Lemma dec_term_correct :                                                    forall t k,
      match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
      | in_dead       => dead_ckind k
      end.

  Proof.
    destruct t,k; simpl.
    - destruct c; destruct t; auto.
    - auto.
  Qed.


  Lemma dec_term_from_dead :                                                  forall t k,
      dead_ckind k -> dec_term t k = in_dead.

  Proof. inversion 1. Qed.


  Lemma dec_context_correct :                                              forall ec k v,
      match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.

  Proof.
    destruct ec, k, v.
    destruct p1; simpl.
    - auto.
    - unfold elem_plug. 
      repeat (f_equal; eauto using pcons2_and_pcons).
  Qed.


  Lemma dec_context_from_dead :                          forall ec k (v : value (k+>ec)),
      dead_ckind (k+>ec) -> dec_context ec k v = in_dead.

  Proof. inversion 1. Qed.


  Lemma dec_term_next_alive : forall t k {t0 ec0}, 
      dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).
  Proof. auto. Qed.


  Lemma dec_context_next_alive : forall ec k v {t0 ec0}, 
      dec_context ec k v = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).
  Proof. auto. Qed.


  Lemma dec_context_not_val : 
      forall ec {k} (v1 : value k) v0, 
          dec_context ec k v0 <> in_val v1.
  Proof.
    intros ec k v1 v0 H.
    destruct ec, k, v0.
    destruct p1;
    inversion H.
  Qed.


  Lemma dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.
  Proof.
    intros k v.
    destruct v, k.
    auto.
  Qed.




  Definition search_order : ckind -> term -> elem_context -> elem_context -> Prop := 
      fun _ _ _ _ => False.

  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
               (at level 70, t, ec1, ec2 at level 50, no associativity).


  Lemma dec_term_term_top : 
      forall t k {t' ec}, dec_term t k = in_term t' ec -> 
          forall ec',  ~ k, t |~ ec << ec'.
  Proof. auto. Qed.


  Lemma dec_context_red_bot : 
      forall k ec v {r : redex k}, dec_context ec k v = in_red r -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.
  Proof. auto. Qed.


  Lemma dec_context_val_bot : 
      forall k ec v {v' : value k}, dec_context ec k v = in_val v' -> 
          forall ec',  ~ k, ec:[v] |~ ec' << ec.
  Proof. auto. Qed.


  Lemma dec_context_term_next : 
      forall ec0 k v {t ec1}, dec_context ec0 k v = in_term t ec1 -> 
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.
  Proof.
    intros ec k; destruct ec, k, v.
    destruct p1;
    inversion 1.
  Qed.


  Lemma elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.
  Proof. inversion 2. Qed.


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. intros k t ec. constructor. inversion 1. Qed.


  Lemma search_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.
  Proof. auto. Qed.


  Lemma search_order_trans   : forall k t ec0 ec1 ec2,
      k, t |~ ec0 << ec1 -> k, t |~ ec1 << ec2 -> k,t |~ ec0 << ec2.
  Proof. auto. Qed.


  Lemma search_order_comp_if : 
      forall t ec0 ec1 k, immediate_ec ec0 t -> immediate_ec ec1 t -> 
          ~ dead_ckind (k+>ec0) -> ~ dead_ckind (k+>ec1) ->
              k, t |~ ec0 << ec1  \/  k, t |~ ec1 << ec0  \/  ec0 = ec1.
  Proof.
    intros t ec0 ec1 k H1 H2 H3 H4.
    destruct H1 as [t' H1], H2 as [t'' H2].
    destruct ec0, ec1, t; inversion H1; inversion H2; subst.
    inversion H7; subst.
    auto.
  Qed.


  Lemma search_order_comp_fi : 
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->  
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
              ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof. inversion 1. Qed.

End Lam_KES_CBN_Strategy.



Module Lam_KES_CBN_RefSem := PreciseRedRefSem Lam_KES_CBN_PreRefSem Lam_KES_CBN_Strategy.



Import Lam_KES_CBN_PreRefSem Lam_KES_CBN_RefSem.

Instance Lam_KES_CBN_SafeReg : SafeKRegion init_ckind closed.
Proof. split.

(*preservation:*) {
  intros t1 t2 H1 [k [c [r [t [H2 [H3 ?]]]]]].
  destruct H2 as [_ H2].
  subst.
  destruct (red_step_closed _ _ H1) as [t0 [H4 H5]].
  congruence.
}

(*progress:*) {
  intros t1 H1.
  destruct (decompose t1 init_ckind init_ckind_alive) as [[k r c | v] [? H2]];
      subst.
  - right.
    destruct (red_step_closed _ _ H1) as [t [H2 H3]].
    exists c[t].
    exists _, c, r, t.
    unfold dec; eauto.
  - left. exists v; auto.
}
Qed.


Require Import refocusing_machine.

Module EAKrivineMachine := RefEvalApplyMachine Lam_KES_CBN_RefSem.
(*Module KrivinMachine := 
    RefPushEnterMachine Lam_KES_CBN_Cal.RedLang Lam_KES_CBN_RefSem.*)


Module Example.

  Require Import refocusing_machine_facts.

  Module RAWF := SloppyRefEvalApplyMachine_Facts  Lam_KES_CBN_RefSem 
                                                  EAKrivineMachine.RAW.
  Import  Lam_KES_CBN_RefSem  EAKrivineMachine.RAW  RAWF.


  Example id_term   := Cl (Lam0 POne (Var0 0 0)) (PSingle nil).
  Example id_closed : closed id_term.
  Proof. repeat constructor; simpl; auto. Qed.


  Variables 
  (t        : term)
  (t_closed : closed t).

  Example t_id_term := App t id_term.

  Example t_id_step_closed : 
      exists st, (c_eval t (id_term=:[.])) → st /\ closed (decompile st).

  Proof with simpl; eauto.
    assert (H := init_ckind_alive).
    destruct (progress (c_eval t (id_term=:[.]))) as [[? H1] | [st H1]].
    {
        repeat split...
        - apply t_closed.
        - repeat constructor.
    }
    - inversion H1.
    - exists st; split...
      apply preservation in H1.
      + intuition.
      + repeat split...
        * apply t_closed.
        * repeat constructor.
  Qed.

End Example.

