

(* Lambda calculus with normal order and substitutions in one step example *)


Require Import Program
               Util
               refocusing_semantics.



Module Lam_NO_PreRefSem <: PRE_REF_SEM.

  Parameter var : Set.


  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr.
  Definition term := expr.
  Hint Unfold term.

  Inductive ck := Eᵏ | Fᵏ | Botᵏ.
  Definition ckind := ck.
  Hint Unfold  ckind.


  Inductive val : ckind -> Type :=

  | vELam : var -> val Eᵏ -> val Eᵏ
  | vEVar : var -> val Eᵏ
  | vEApp : valA -> val Eᵏ -> val Eᵏ
  
  | vFLam : var -> term -> val Fᵏ
  | vFVar : var -> val Fᵏ
  | vFApp : valA -> val Eᵏ -> val Fᵏ
  
  | vBot  : term -> val Botᵏ
  
  with valA :=

  | vAVar : var -> valA
  | vAApp : valA -> val Eᵏ -> valA.


  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val Sort Prop
    with valCa_Ind := Induction for valA Sort Prop.


  Inductive red : ckind -> Type :=
  | rEApp : var -> term -> term -> red Eᵏ
  | rFApp : var -> term -> term -> red Fᵏ.
  Definition redex := red.
  Hint Unfold redex.


  Inductive ec :=
  | lam_c : var -> ec
  | ap_r  : term -> ec
  | ap_l  : valA -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | Eᵏ => match ec with lam_c _ => Eᵏ   | ap_r _ => Fᵏ | ap_l _ => Eᵏ end
      | Fᵏ => match ec with lam_c _ => Botᵏ | ap_r _ => Fᵏ | ap_l _ => Eᵏ end
      | _  => Botᵏ
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


  Definition init_ckind : ckind     :=  Eᵏ.
  Definition dead_ckind (k : ckind) :=  k = Botᵏ.
  Hint Unfold init_ckind dead_ckind.


  Lemma death_propagation : 
      forall k ec, dead_ckind k -> dead_ckind (k+>ec).

  Proof.
    intros k ec H.
    destruct k;
    inversion H;
    reflexivity.
  Qed.


  Inductive context (k1 : ckind) : ckind -> Set :=
  | empty : context k1 k1
  | ccons : forall (ec : elem_context) {k2}, context k1 k2 -> context k1 (k2+>ec).
  Arguments empty {k1}. Arguments ccons {k1} _ {k2} _.

  Notation "[.]"      := empty.
  Notation "[.]( k )" := (@empty k).
  Infix "=:"          := ccons (at level 60, right associativity).


  Fixpoint value_to_term {k} (v : value k) : term :=
      match v with
      | vELam x v => Lam x (value_to_term v)
      | vEVar x => Var x
      | vEApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      | vFLam x t => Lam x t
      | vFVar x => Var x
      | vFApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      | vBot t => t
      end

  with valA_to_term v : term :=
      match v with
      | vAVar x => Var x
      | vAApp v1 v2 => App (valA_to_term v1) (value_to_term v2)
      end.

  Coercion value_to_term : value >-> term.
  Coercion valA_to_term  : valA >-> term.


  Definition redex_to_term {k} (r : redex k) : term :=
      match r with
      | rEApp x t1 t2   => App (Lam x t1) t2
      | rFApp x t1 t2 => App (Lam x t1) t2
      end.
  Coercion redex_to_term : redex >-> term.


  Lemma init_ckind_alive : ~dead_ckind init_ckind.
  Proof. auto. Qed.


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma valA_to_term_injective :
      forall v v', valA_to_term v = valA_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valA,    valA_to_term v  = valA_to_term v'  -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;

    solve
    [ destruct r; 
      dependent destruction r'; 
      inversion H;
      f_equal; auto ].
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
      | lam_c x => Lam x t
      | ap_r tr => App t tr
      | ap_l v  => App (v : term) t
      end.
  Notation "ec :[ t ]" := (elem_plug t ec) (at level 0).


  Lemma elem_plug_injective1 : forall ec {t0 t1}, ec:[t0] = ec:[t1] -> t0 = t1.

  Proof.
    intros ec t0 t1 H.
    destruct ec;
    solve [ injection H; trivial ].
  Qed.


  Fixpoint plug t {k1 k2} (c : context k1 k2) : term :=
      match c with
      | [.]    => t 
      | ec=:c' => plug ec:[t] c'
      end.
  Notation "c [ t ]" := (plug t c) (at level 0).


  Definition immediate_ec ec t := exists t', ec:[t'] = t.


  Parameter subst : var -> term -> term -> term.


  Definition contract0 {k} (r : redex k) : term :=
      match r with
      | rEApp x t0 t1 => subst x t1 t0
      | rFApp x t0 t1 => subst x t1 t0
      end.
  Definition contract {k} (r : redex k) := Some (contract0 r).


  Instance dead_is_comp : CompPred ckind dead_ckind.
      split. destruct x; auto.
  Defined.


  Lemma valA_is_valF : 
      forall v1 : valA, exists v2 : value Fᵏ, valA_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vFVar v)...
    - exists (vFApp v1 v)...
  Qed.


  Lemma value_trivial1 : forall {k} ec t, 
      forall (v : value k), ~dead_ckind (k+>ec) -> ec:[t] = v ->
          exists (v' : value (k+>ec)), t = v'.
  Proof.
    intros k ec t v H H0.
    destruct ec, v; inversion H0; subst; 
    solve 
    [ eautof
    | auto using valA_is_valF ].
  Qed.


  Lemma redex_trivial1 : forall {k} (r : redex k) ec t,
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.
  Proof with auto.
    intros k r ec t H H0.
    destruct ec, r; inversion H0; subst;
    solve 
    [ eexists (vFLam _ _); reflexivity
    | eauto using valA_is_valF
    | destruct v; inversion H2 ].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (valA_to_term ?v) _ <> _ => dependent_destruction2 v
    end;

    solve [ discriminate ].
  Qed.


  Lemma proper_death : forall k, dead_ckind k -> ~ exists (r : redex k), True.
  Proof with eauto.
    intros k H [r _].
    destruct r; 
    solve [inversion H].
  Qed.


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


  Definition dec (t : term) k (d : decomp k) : Prop := 
      ~dead_ckind k /\ t = d.


  Definition immediate_subterm t0 t := exists ec, t = ec:[t0].

  Lemma wf_immediate_subterm : well_founded immediate_subterm.
  Proof. REF_LANG_Help.prove_st_wf. Qed.


  Definition subterm_order := clos_trans_1n term immediate_subterm.
  Notation "t1 <| t2" := (subterm_order t1 t2) (at level 70, no associativity).
  Definition wf_subterm_order : well_founded subterm_order 
      := wf_clos_trans_l _ _ wf_immediate_subterm.


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

End Lam_NO_PreRefSem.




Module Lam_NO_Strategy <: REF_STRATEGY Lam_NO_PreRefSem.

  Import Lam_NO_PreRefSem.


  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_dead : interm_dec k.
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k} _ _. Arguments in_dead {k}.


  Definition dec_term t k : interm_dec k :=

      match k as k0 return interm_dec k0 with 
      | Eᵏ   => match t with
                | App t1 t2 => in_term t1 (ap_r t2)
                | Var x     => in_val (vEVar x)
                | Lam x t1  => in_term t1 (lam_c x)
                  end
      | Fᵏ   => match t with
                | App t1 t2 => in_term t1 (ap_r t2)
                | Var x     => in_val (vFVar x)
                | Lam x t1  => in_val (vFLam x t1)
                end
      | Botᵏ => in_dead
      end.


  Definition dec_context ec k (v : value (k+>ec)) : interm_dec k :=

      match ec as ec0 return value (k+>ec0) -> interm_dec k with

      | lam_c x  => match k as k0 return value (k0+>lam_c x) -> interm_dec k0 with
                    | Eᵏ   => fun v => in_val (vELam x v)
                    | Fᵏ   => fun v => in_dead
                    | Botᵏ => fun v => in_dead
                    end

      | ap_r t   => match k as k0 return value (k0+>(ap_r t)) -> interm_dec k0 with
                    | Eᵏ   => fun v => 
                                  match v with
                                  | vFLam x t0  => in_red (rEApp x t0 t)
                                  | vFVar x     => in_term t (ap_l (vAVar x))
                                  | vFApp v1 v2 => in_term t (ap_l (vAApp v1 v2))
                                  | _ => @in_dead Eᵏ
                                  end
                    | Fᵏ   => fun v => 
                                  match v with
                                  | vFLam x t0  => in_red (rFApp x t0 t)
                                  | vFVar x     => in_term t (ap_l (vAVar x))
                                  | vFApp v1 v2 => in_term t (ap_l (vAApp v1 v2))
                                  | _ => @in_dead Fᵏ
                                  end
                    | Botᵏ => fun v => in_dead
                    end

      | ap_l v0  => match k as k0 return value (k0+>(ap_l v0)) -> interm_dec k0 with
                    | Eᵏ   => fun v => in_val (vEApp v0 v)
                    | Fᵏ   => fun v => in_val (vFApp v0 v)
                    | Botᵏ => fun v => in_dead
                    end
      end v.


  Lemma dec_term_correct : 
      forall (t : term) k, match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
      | in_dead       => dead_ckind k 
      end.

  Proof.
    destruct k, t; simpl; 
    auto.
  Qed.


  Lemma dec_term_from_dead : forall t k, dead_ckind k -> dec_term t k = in_dead.
  Proof.
    intros t k H.
    destruct k;
    solve [ autof ].
  Qed.


  Lemma dec_term_next_alive : 
      forall t k t0 ec0, dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

  Proof.
    intros t k t0 ec0 H.
    destruct t, k;
    solve [ inversion H; subst; 
            auto ].
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
    destruct ec, k;
    solve [ autof ].
  Qed.


  Lemma dec_context_next_alive : forall ec k v {t ec0}, 
      dec_context ec k v = in_term t ec0 -> ~ dead_ckind (k+>ec0).

  Proof.
    intros ec k v t ec0 H.
    destruct ec, ec0, k; dependent destruction v;  
    solve [ autof ].
  Qed.


  Definition search_order (k : ckind) (t : term) (ec ec0 : elem_context) : Prop :=
      match k with
      | Botᵏ => False
      | _    => match ec, ec0 with 
                | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
                | _, _           => False
                end
      end.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
                                     (no associativity, at level 70, ec1, t at level 69).


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_trans :  forall k t ec0 ec1 ec2, 
      k,t |~ ec0 << ec1 -> k,t |~ ec1 << ec2 -> 
      k,t |~ ec0 << ec2.

  Proof.
    intros k t ec0 ec1 ec2 H H0.
    destruct k, ec0, ec1;
    solve [ autof ].
  Qed.


  Lemma search_order_comp_if :                                        forall t ec0 ec1 k,
      immediate_ec ec0 t -> immediate_ec ec1 t -> 
      ~dead_ckind (k+>ec0) -> ~dead_ckind (k+>ec1) ->
          k, t |~ ec0 << ec1 \/ k,t |~ ec1 << ec0 \/ ec0 = ec1.

  Proof.
    intros t k ec0 ec1 H0 H1 H2 H3.

    destruct H0 as (t0, H4); destruct H1 as (t1, H5).
    subst t.
    destruct k, ec0, ec1;
    inversion H5; subst;

    solve
    [ compute; eautof 7
    | do 2 right; 
      f_equal;
      apply valA_to_term_injective; auto ].
  Qed.


  Lemma search_order_comp_fi :
      forall k t ec0 ec1,  k, t |~ ec0 << ec1 ->
          immediate_ec ec0 t /\ immediate_ec ec1 t /\ 
          ~ dead_ckind (k+>ec0) /\ ~ dead_ckind (k+>ec1).

  Proof with auto.
    intros k t ec0 ec1 H.
    destruct k, ec0, ec1;
    inversion H;
    solve [auto].
  Qed.


  Lemma dec_term_term_top : forall t k {t' ec}, 
            dec_term t k = in_term t' ec -> forall ec', ~ k, t |~ ec << ec'.

  Proof.
    intros t k t' ec H ec' H0.
    destruct k, t, ec'; 
    solve [ inversion H; subst; inversion H0 ].
  Qed.


  Lemma dec_context_red_bot : 
      forall k ec v r, dec_context ec k v = in_red r -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k ec v r H ec'.
    destruct k, ec, ec'; dependent destruction v;
    solve
    [ autof
    | inversion H;
      intro G;
      unfold search_order in G; destruct G as (G, _);
      destruct G as (t1, G); inversion G; subst;
      destruct v0; 
      autof ].
  Qed.


  Lemma dec_context_val_bot : 
      forall k ec v v', dec_context ec k v = in_val v' -> 
          forall ec', ~ k, ec:[v] |~ ec' << ec.
  Proof.
    intros k ec v v' H ec'.
    destruct k, ec, ec'; dependent destruction v; 
    solve [ autof ].
  Qed.


  Lemma dec_context_term_next : 
      forall ec0 k v t ec1, dec_context ec0 k v = in_term t ec1 ->
      (*1*) k, ec0:[v] |~ ec1 << ec0 /\ 
      (*2*) forall ec,  k, ec0:[v] |~ ec << ec0  ->  ~ k, ec0:[v] |~ ec1 << ec.

  Proof.
    intros ec0 k v t ec1 H.
    destruct k, ec0, ec1; dependent destruction v; 
    solve 
    [ autof

    | inversion H; subst;
      split;
      [ constructor; 
        compute; eauto
      | intros ec'' H0 H1; 
        destruct ec'';
        solve [ autof ] 
      ] ].
  Qed.


  Lemma elem_context_det : 
      forall t ec {t'}, t = ec:[t'] -> 
          forall k ec',  k, t |~ ec' << ec -> 
              exists (v : value (k+>ec)), t' = v.

  Proof.
    intros t ec0 t' H k ec' H0.
    subst.

    destruct k, ec0, ec'; autof;
    unfold search_order in H0; destruct H0 as (H, _);
    destruct (valA_is_valF v) as (v0, H0);

    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End Lam_NO_Strategy.



Module Lam_NO_RefSem := PreciseRedRefSem Lam_NO_PreRefSem Lam_NO_Strategy.



Require Import refocusing_machine.

Module Lam_NO_EAM := RefEvalApplyMachine Lam_NO_RefSem.
