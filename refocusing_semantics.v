Require Export reduction_semantics.



Module Type RED_REF_SEM (R : RED_LANG).

  Declare Module DEC : DEC_STEP R.
  Import R.
  Export DEC.


  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> forall {k1 k2}, context k1 k2 -> decomp k1 -> Prop :=

  | d_dec  : forall t {k1 k2} (c : context k1 k2) {r},
               dec_term t k2 = in_red r -> 
               dec t c (d_red r c)
  | d_v    : forall t {k1 k2} {c : context k1 k2} {v d},
               dec_term t k2 = in_val v ->
               decctx v c d ->
               dec t c d
  | d_term : forall t {t0 k1 k2} {c : context k1 k2} {ec d},
               dec_term t k2 = in_term t0 ec ->
               dec t0 (ec=:c) d ->
               dec t c d

  with decctx : forall {k2}, value k2 -> 
                    forall {k1}, context k1 k2 -> decomp k1 -> Prop :=

  | dc_end  : forall {k} (v : value k), 
                ~ dead_ckind k ->
                decctx v [.] (d_val v)
  | dc_dec  : forall ec {k2} (v : value (k2+>ec)) {k1} (c : context k1 k2) {r},
                dec_context ec k2 v = in_red r ->
                decctx v (ec=:c) (d_red r c)
  | dc_val  : forall {k2} {v0 : value k2} ec (v : value (k2+>ec)) 
                     {k1} {c  : context k1 k2} {d},
                dec_context ec k2 v = in_val v0 ->
                decctx v0 c d ->
                decctx v (ec=:c) d
  | dc_term : forall ec {ec0 k2} (v : value (k2+>ec)) 
                            {k1} {c : context k1 k2} {t d},
                dec_context ec k2 v = in_term t ec0 ->
                dec t (ec0=:c) d ->
                decctx v (ec=:c) d.

  Scheme dec_Ind    := Induction for dec Sort Prop
    with decctx_Ind := Induction for decctx Sort Prop.


  Axiom dec_val_self : forall {k2} (v : value k2) {k1} {c : context k1 k2} {d}, 
                           dec v c d <-> decctx v c d.


  Declare Module RS : RED_SEM R with Definition dec := dec.
  Export RS.

End RED_REF_SEM.



Require Import Util.
Require Import Program.
Require Import reduction_lang_facts.


Module Red_Sem_Proper (R : RED_LANG) (RS : RED_REF_SEM R) : RED_SEM_PROPER R RS.RS.

  Import R.
  Module RLF := RED_LANG_Facts R.
  Import RLF.
  Import RS.
  Export DEC.


  Lemma dec_is_function : forall {t k} {d d0 : decomp k}, 
                              decempty t d -> decempty t d0 -> d = d0.
  Proof.
    intros t k d1 d2 DE1 DE2.
    dependent destruction DE1; dependent destruction DE2.

    induction H using dec_Ind with 
    (P  := fun t _ _ c d _ => forall d0, dec t c d0    -> d = d0)
    (P0 := fun _ v _ c d _ => forall d0, decctx v c d0 -> d = d0);

    intros;

    (* automated cases *)
    match goal with

    | [ RD : (dec ?t ?c ?d), DT1 : (dec_term ?t ?k = _) |- _ ] => 
             inversion RD; dep_subst; 
             match goal with DT2 : (dec_term ?t ?k = _) |- _ => 
                 rewrite DT2 in DT1; inversion DT1 end

    | [ RC : (decctx ?v (?ec=:?c) ?d), DC1 : (dec_context ?ec ?k ?v = _) |- _ ] => 
             dependent_destruction2 RC; inversion_ccons x2; dep_subst;
             match goal with DC2 : (dec_context ?ec' ?k' ?v' = _) |- _ => 
                 rewrite DC2 in DC1; inversion DC1 end

    | [ RC : (decctx ?v [.] ?d) |- _] => 
             dependent_destruction2 RC

    end;

    subst; eauto.
  Qed.
  Hint Resolve dec_is_function : prop.


  Lemma iter_is_function : forall {k} {d : decomp k} {v v0}, 
                               iter d v -> iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    - dependent destruction H...
    - dependent destruction H2; subst. 
      rewrite H2 in H; inversion H; subst.
      apply IHiter.
      cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.


  Lemma eval_is_function : forall {t} {v v0 : value init_ckind}, 
                               eval t v -> eval t v0 -> v = v0.
  Proof with eauto with prop.
    intros.
    dependent destruction H.
    dependent destruction H1.
    cutrewrite (d = d0) in H0...
  Qed.


  Lemma dec_correct : forall {t k1 k2} {c : context k1 k2} {d}, 
                          dec t c d -> decomp_to_term d = c[t].
  Proof.
    induction 1 using dec_Ind with
    (P := fun t _ _ c d (H : dec t c d)     => decomp_to_term d = c[t])
    (P0:= fun _ v _ c d (H:RS.decctx v c d) => decomp_to_term d = c[v]);
    simpl; auto;

    first
    [ assert (G := dec_term_correct t k2);       rewrite e in G
    | assert (G := dec_context_correct ec k2 v); rewrite e in G ]; 
    
    simpl in *; 
    try rewrite IHdec;
    congruence.
  Qed.


  Lemma dec_total : forall t k, ~ dead_ckind k -> exists (d : decomp k), decempty t d.
  Proof with auto.
    intros t k H.
    destruct (decompose t k H) as [(v, ?) | (?, (r, (c, ?)))]; 
    intros; subst.
    - exists (d_val v); constructor.
      rewrite dec_val_self.
      constructor...
    - exists (d_red r c); constructor.
      apply dec_plug_rev.
        { apply (proper_death2 _ _ [.] r). }
      rewrite <- compose_empty.
      apply dec_redex_self.
  Qed.


  Lemma unique_decomposition :

      forall (t : term) k1, ~ dead_ckind k1 ->
          (exists v : value k1, t = v) \/ 
          (exists k2 (r : redex k2) (c : context k1 k2),  t = c[r] /\ 
	      forall k2' (r0 : redex k2') (c0 : context k1 k2'), 
                  t = c0[r0] -> k2' = k2 /\ r ~= r0 /\ c ~= c0).

  Proof with eauto.
    intros.
    destruct (decompose t k1 H) as [(v, H0) | (k', (r, (c, H0)))].
    - left; exists v...
    - right; exists k' r; exists c; split.
      + congruence.
      + intros.
        assert (H2 : decempty t (d_red r c) /\ decempty t (d_red r0 c0)).
        {
            split;
            constructor; 
            [ rewrite H0 | rewrite H1 ]; 
            apply dec_plug_rev;
            solve
            [ apply (proper_death2 _ _ [.]); auto
            | rewrite <- compose_empty; apply dec_redex_self ]. 
        }
        destruct H2.
        assert (H4 := dec_is_function H2 H3); dependent destruction H4.
        intuition.
  Qed.

End Red_Sem_Proper.




Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module RefSem : RED_REF_SEM R.
  Import R.
  Export RefSem.

  Axiom dec_context_not_val : 
      forall ec {k} v (v0 : value k), dec_context ec k v <> in_val v0.
  Axiom dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.

End PE_REF_SEM.