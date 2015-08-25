Require Import reduction_semantics.



Module Type REF_STEP (R : RED_LANG).

  Import R.


  (* interm_dec k - result of functions performing one step of decomposition of 
                    a term t from the symbol k to a redex.
     in_red r      - t is a redex, t = r.
     in_term t' ec - t = ec[t'] and to find a redex we are going to check t'.
     in_val v      - there is no redexes in t, t = v.
     in_dead       - result of the functions for arguments out of their domains. *)
  Inductive interm_dec k : Set :=
  | in_red  : redex k -> interm_dec k
  | in_term : term -> elem_context -> interm_dec k
  | in_val  : value k -> interm_dec k
  | in_dead : interm_dec k.
  Arguments in_red {k} _.    Arguments in_val {k} _.
  Arguments in_term {k} _ _. Arguments in_dead {k}.


  (* dec_term t k       - one step of decomposition of t from the symbol k if we
                          have no information about subterms of t. 
                          Domain:  term * { k : ckind | k is not dead }  
     dec_context ec k v - one step of decomposition of a term ec[t] with an additional
                          piece of information saying that t is a value v. 
                          Domain:  elem_context * { (k, v) | k+>ec is not dead and
                                                             v : value (k+>ec)     }  *)
  Parameter dec_term    : term -> forall k, interm_dec k.
  Parameter dec_context : forall ec k, value (k+>ec) -> interm_dec k.


  Axiom dec_term_correct : 
      forall t k, match dec_term t k with
      | in_red r      => t = r
      | in_val v      => t = v
      | in_term t' ec => t = ec:[t']
      | in_dead       => dead_ckind k 
      end.

  Axiom dec_term_from_dead : forall t k, 
      dead_ckind k -> dec_term t k = in_dead.


  Axiom dec_context_correct : 
      forall ec k v, match dec_context ec k v with
      | in_red r      => ec:[v] = r
      | in_val v'     => ec:[v] = v'
      | in_term t ec' => ec:[v] = ec':[t]
      | in_dead       => dead_ckind (k+>ec) 
      end.

  Axiom dec_context_from_dead : forall ec k (v : value (k+>ec)), 
      dead_ckind (k+>ec) -> dec_context ec k v = in_dead.


  (* Any decomposition build by applying dec_term and dec_context needs to be proper. *)
  Axiom dec_term_next_alive : forall t k {t0 ec0}, 
      dec_term t k = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

  Axiom dec_context_next_alive : forall ec k v {t0 ec0}, 
      dec_context ec k v = in_term t0 ec0 -> ~ dead_ckind (k+>ec0).

End REF_STEP.
