Require Export reduction_semantics.
Require Export strategy_step.


(* Refocusing semantics *)

Module Type RED_REF_SEM (R : RED_LANG).

  Declare Module ST : STRATEGY_STEP R.
  Import R.
  Export ST.


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




(* Push-enter refocusing semantics *)

Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module RefSem : RED_REF_SEM R.
  Import R.
  Export RefSem.

  Axiom dec_context_not_val : 
      forall ec {k} v1 (v0 : value (k+>ec)), dec_context ec k v0 <> in_val v1.

  Axiom dec_term_value : 
      forall {k} (v : value k), dec_term v k = in_val v.

End PE_REF_SEM.
