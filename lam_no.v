Require Import Program.
Require Import Util.
Require Import refocusing_semantics.
Require Import reduction_languages_facts.




Module Lam_NO_RefLang <: REF_LANG.

  Parameter var : Set.


  Inductive expr :=
  | App : expr -> expr -> expr
  | Var : var -> expr
  | Lam : var -> expr -> expr.
  Definition term := expr.
  Hint Unfold term.


  Inductive ck := C | ECa | CBot.
  Definition ckind := ck.
  Hint Unfold  ckind.


  Inductive val : ckind -> Type :=

  | vCLam   : var -> val C -> val C
  | vCVar   : var -> val C
  | vCApp   : valCa -> val C -> val C
  
  | vECaLam : var -> term -> val ECa
  | vECaVar : var -> val ECa
  | vECaApp : valCa -> val C -> val ECa
  
  | vCBot   : term -> val CBot
  
  with valCa :=

  | vCaVar : var -> valCa
  | vCaApp : valCa -> val C -> valCa.


  Definition value := val.
  Hint Unfold value.

  Scheme val_Ind   := Induction for val Sort Prop
    with valCa_Ind := Induction for valCa Sort Prop.


  Inductive red : ckind -> Type :=
  | rCApp   : var -> term -> term -> red C
  | rECaApp : var -> term -> term -> red ECa.
  Definition redex := red.
  Hint Unfold redex.


  Inductive ec :=
  | lam_c : var -> ec
  | ap_r  : term -> ec
  | ap_l  : valCa -> ec.
  Definition elem_context := ec.
  Hint Unfold elem_context.


  Definition ckind_trans (k : ckind) (ec : elem_context) := 
      match k with
      | C    => match ec with lam_c _ => C    | ap_r _ => ECa | ap_l _ => C end
      | ECa  => match ec with lam_c _ => CBot | ap_r _ => ECa | ap_l _ => C end
      | _    => CBot
      end.
  Notation "k +> ec" := (ckind_trans k ec) (at level 50, left associativity).


  Definition init_ckind : ckind     :=  C.
  Definition dead_ckind (k : ckind) :=  k = CBot.
  Hint Unfold init_ckind dead_ckind.


  Lemma death_propagation : 
      forall k, dead_ckind k -> forall ec, dead_ckind (k+>ec).

  Proof.
    intros k H.
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
      | rCApp x t1 t2   => App (Lam x t1) t2
      | rECaApp x t1 t2 => App (Lam x t1) t2
      end.
  Coercion redex_to_term : redex >-> term.


  Lemma value_to_term_injective : 
      forall {k} (v v' : value k), value_to_term v = value_to_term v' -> v = v'.

  Proof with auto.
    induction v using val_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma valCa_to_term_injective : 
      forall v v', valCa_to_term v = valCa_to_term v' -> v = v'.

  Proof with auto.
    induction v using valCa_Ind with 
    (P  := fun k v => forall v' : value k, value_to_term v = value_to_term v' -> v = v')
    (P0 := fun v   => forall v' : valCa,   valCa_to_term v = valCa_to_term v' -> v = v');
    dependent destruction v'; intro H; inversion H; f_equal...
  Qed.


  Lemma redex_to_term_injective : 
      forall {k} (r r' : redex k), redex_to_term r = redex_to_term r' -> r = r'.

  Proof with auto.
    intros k r r' H.
    destruct k;

    solve
    [ induction r; 
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
      | rCApp   x t0 t1 => subst x t1 t0
      | rECaApp x t0 t1 => subst x t1 t0
      end.
  Definition contract {k} (r : redex k) := Some (contract0 r).


  Lemma valCa_is_valECa : 
      forall v1 : valCa, exists v2 : value ECa, valCa_to_term v1 = value_to_term v2.

  Proof with auto.
    destruct v1; intros.
    - exists (vECaVar v)...
    - exists (vECaApp v1 v)...
  Qed.


  Lemma value_trivial1 : forall {k} (v : value k) ec t, 
                             ~dead_ckind (k+>ec) -> ec:[t] = v ->
                                 exists (v' : value (k+>ec)), t = v'.
  Proof.
    intros k v ec t H H0.
    destruct ec, v; inversion H0; subst; 
    solve 
    [ eautof
    | auto using valCa_is_valECa ].
  Qed.


  Lemma redex_trivial1 : forall {k} (r : redex k) ec t,
                             ~dead_ckind (k+>ec) -> ec:[t] = r -> 
                                 exists (v : value (k+>ec)), t = v.
  Proof with auto.
    intros k r ec t H H0.
    destruct ec, r; inversion H0; subst;
    solve 
    [ eexists (vECaLam _ _); reflexivity
    | eauto using valCa_is_valECa
    | destruct v; inversion H2 ].
  Qed.


  Lemma value_redex : forall {k} (v : value k) (r : redex k), 
                          value_to_term v <> redex_to_term r.
  Proof.
    intros k v r.

    dependent destruction r; dependent destruction v; 
    simpl;
    try match goal with 
    | |- App (valCa_to_term ?v) _ <> _ => dependent_destruction2 v
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
      | d_red _ r c => c[r]
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


  Notation "k |~ t1 → t2"  := (reduce k t1 t2)           
                                         (no associativity, at level 70, t1 at level 69).
  Notation "k |~ t1 →+ t2" := (clos_trans_1n _ (reduce k) t1 t2) 
                                         (no associativity, at level 70, t1 at level 69).
  Notation "k |~ t1 →* t2" := (clos_refl_trans_1n _ (reduce k) t1 t2) 
                                         (no associativity, at level 70, t1 at level 69).


End Lam_NO_RefLang.




Module Lam_NO_Strategy <: REF_STRATEGY Lam_NO_RefLang.

  Import Lam_NO_RefLang.


  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_dead : interm_dec k.
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k} _ _. Arguments in_dead {k}.


  Definition dec_term t k : interm_dec k :=

      match k as k0 return interm_dec k0 with 
      | C    => match t with
                | App t1 t2 => in_term t1 (ap_r t2)
                | Var x     => in_val (vCVar x)
                | Lam x t1  => in_term t1 (lam_c x)
                  end
      | ECa  => match t with
                | App t1 t2 => in_term t1 (ap_r t2)
                | Var x     => in_val (vECaVar x)
                | Lam x t1  => in_val (vECaLam x t1)
                end
      | CBot => in_dead
      end.


  Definition dec_context ec k (v : value (k+>ec)) : interm_dec k :=

      match ec as ec0 return value (k+>ec0) -> interm_dec k with

      | lam_c x  => match k as k0 return value (k0+>lam_c x) -> interm_dec k0 with
                    | C    => fun v => in_val (vCLam x v)
                    | ECa  => fun v => in_dead
                    | CBot => fun v => in_dead
                    end

      | ap_r t   => match k as k0 return value (k0+>(ap_r t)) -> interm_dec k0 with
                    | C    => fun v => 
                                  match v with
                                  | vECaLam x t0  => in_red (rCApp x t0 t)
                                  | vECaVar x     => in_term t (ap_l (vCaVar x))
                                  | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                  | _ => @in_dead C
                                  end
                    | ECa  => fun v => 
                                  match v with
                                  | vECaLam x t0  => in_red (rECaApp x t0 t)
                                  | vECaVar x     => in_term t (ap_l (vCaVar x))
                                  | vECaApp v1 v2 => in_term t (ap_l (vCaApp v1 v2))
                                  | _ => @in_dead ECa
                                  end
                    | CBot => fun v => in_dead
                    end

      | ap_l v0  => match k as k0 return value (k0+>(ap_l v0)) -> interm_dec k0 with
                    | C    => fun v => in_val (vCApp v0 v)
                    | ECa  => fun v => in_val (vECaApp v0 v)
                    | CBot => fun v => in_dead
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
      | CBot => False
      | _      => match ec, ec0 with 
                  | ap_l _, ap_r _ => immediate_ec ec t /\ immediate_ec ec0 t 
                  | _, _           => False
                  end
      end.
  Notation "k , t |~  ec1 << ec2 " := (search_order k t ec1 ec2) 
                                     (no associativity, at level 70, ec1, t at level 69).


  Lemma wf_search : forall k t, well_founded (search_order k t).
  Proof. REF_LANG_Help.prove_ec_wf. Qed.


  Lemma search_order_antisym : forall k t ec ec0, 
      k, t |~ ec << ec0 -> ~ k, t |~ ec0 << ec.

  Proof.
    intros k t ec ec0 H.
    destruct k, ec, ec0;
    solve [ autof ].
  Qed.


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
      apply valCa_to_term_injective; auto ].
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
    destruct (valCa_is_valECa v) as (v0, H0);

    solve
    [ exists v0;
      simpl; rewrite <- H0;
      inversion H as (t0, H1); inversion H1; 
      trivial ].
  Qed.

End Lam_NO_Strategy.



Module Lam_NO_RefSem := RedRefSem Lam_NO_RefLang Lam_NO_Strategy.



Require Import refocusing_machine.

Module Lam_NO_EAM := RefEvalApplyMachine Lam_NO_RefSem.
