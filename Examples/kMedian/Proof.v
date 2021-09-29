Require Import Semantics.

Open Scope positive_scope.

Notation i  := (Var.Lvar T.Nat 1).
Notation F0 := (Var.Lvar (T.User Set_of_Points) 2).
Notation F  := (Var.Lvar (T.List (T.User Set_of_Points)) 3).
Notation D  := (Var.Lvar (T.User Set_of_Points) 4).
Notation x  := (Var.Lvar (T.User Point) 5).
Notation y  := (Var.Lvar (T.User Point) 6).
Notation xy  := (Var.Lvar (T.Pair (T.User Point) (T.User Point)) 7).
Notation W  := (Var.Lvar (T.User Set_of_Points) 8).
Notation ret := (Var.Lvar (T.User Set_of_Points) 9).
Notation j  := (Var.Lvar T.Nat 10).

Close Scope positive_scope.

Section PROOF.

 Parameter T:nat.
 Parameter E: env.

 Definition prg :=
  ([ i <- O;  F <-  F0 |::| Nil _ ] ++
   [  while (i <! T) do
     ([ W <- Hd F ] ++
      ([ xy <$- pick_swap W D W (compl W) ] ++ [
       F <- (W |-| (Efst xy) |+| (Esnd xy)) |::| F;
       i <- i +! 1%nat ]))
   ]) ++
  ( [ j <$- pick_solution D F T ] ++ [ ret <- F[{j}] ] ).
 
 Definition Pre := kreq_mem {{ F0 }} /-\ 
   (fun k (m1 m2: Mem.t k) => adj_sets (m1 D) (m2 D)).

 Definition Post := kreq_mem {{ret}}.

 Lemma loop_sem: forall k (m:Mem.t k) f,
   let c:=  [ W <- Hd F; xy <$- pick_swap W D W (compl W);
     F <- (W |-| (Efst xy) |+| (Esnd xy)) |::| F ] in 
   mu ([[ [ while (i <! T) do (c ++ [ i <- i +! 1%nat ]) ] ]] E m) f ==
   mu (drestr ([[ unroll_while (i <! T) (c ++ [ i <- i +! 1%nat ]) T ]] E m) 
     (negP (EP k (i <! T)))) f.
 Proof.
  intros.
  apply deno_bounded_while_elim with (T -! i).
    intros k' m' H' g Hg.
    rewrite deno_app_elim, (@Modify_deno_elim E {{F,xy,W}} c);
      [ | apply modify_correct with (refl1_info (empty_info E E)) 
        Vset.empty; apply eq_refl ].
    match goal with |- _ == fmonot (mu ?d) _ => rewrite <-(mu_zero d) end.
    apply mu_stable_eq; unfold fzero; refine (ford_eq_intro _); intro m''.
    rewrite deno_assign_elim; apply Hg.
    generalize H'; clear; unfold EP; expr_simpl; intro H'.
    apply leb_correct; apply leb_complete in H'; omega.
    intro m'; expr_simpl; intro H'; apply leb_correct_conv; omega.
    expr_simpl; omega.
 Qed.

 Lemma prg_diff_private: 
   eequiv Pre E prg E prg Post 
   (fun _ => exp (2 * eps * Diameter * INR ((T + 1)%nat))) (fun _ => 0).
 Proof.
  unfold prg.
  set (R := fun X => kreq_mem X /-\ (fun k (m1 m2: Mem.t k) 
    => adj_sets (m1 D) (m2 D))).
  apply eequiv_seq_zero with (Q':= R {{i,F}}) 
    (lam  := fun _ => exp (2*eps*Diameter*INR T))
    (lam' := fun _ => exp (2*eps*Diameter)); trivial.
    intros _; rewrite plus_INR, <-exp_plus; apply exp_monotonic; 
      rewrite Rmult_plus_distr_l, S_INR, (proj2 (Rplus_ne _)), Rmult_1_r; trivial.
  apply equiv_seq_eequiv with (Q':= R {{i,F}}).
    intros _; rewrite <-exp_0 at 1; apply exp_monotonic.
    repeat apply Rmult_le_pos; [ fourier | 
      apply eps_pos | | apply pos_INR ];
      rewrite <-(Diam_spec (T.default 0 (T.User Point)) 
        (T.default 0 (T.User Point))); apply Delta_pos.
  (* Initialization *)
  unfold R, Pre; apply equiv_inv_Modify with (M1:={{F,i}}) (M2:={{F,i}}) 
    (X1:={{D}}) (X2:={{D}}); try apply eq_refl.
    intros k m1 m2 m1' m2' H1 H2; rewrite (H1 _ D), (H2 _ D); auto with set.
    apply modify_correct with (refl1_info (empty_info E E)) Vset.empty, eq_refl.
    apply modify_correct with (refl1_info (empty_info E E)) Vset.empty, eq_refl.
  eqobs_in.
  (* Loop *)
  apply eequiv_weaken with
    (P' := R {{i,F}} /-\ EP_eq_expr (i <! T) (i <! T))
    (Q' := R {{i,F}} /-\ ~- EP1 (i <! T) /-\ ~- EP2 (i <! T))
    (lam' := fun _ => (exp (2 * eps * Diameter) ^ T)%R)
    (ep' := fun _ => sum_powR (exp (2 * eps * Diameter)) 0 T).
    intros k m1 m2 H; split; trivial; destruct H as (H1,_);
      unfold EP_eq_expr; expr_simpl; rewrite (H1 _ i); auto with set.
    intros k m1 m2 (?,_); trivial.
    intros _; generalize (2 * eps * Diameter)%R; intro r.
    induction T.
      rewrite Rmult_0_r, exp_0; trivial.
      rewrite S_INR, Rmult_plus_distr_l, exp_plus, Rmult_1_r; simpl.
      rewrite Rmult_comm; apply Rmult_le_compat; trivial;
        [ apply pow_le | ]; left; apply exp_pos.
    intros _; generalize (exp (2 * eps * Diameter)); intro r; apply Oeq_le.
      induction T; simpl; [ | rewrite IHn, multRU_0_r]; trivial.
  apply eequiv_while; trivial.
    intros k m1 m2 _; split; refine (ford_eq_intro _); 
      intro f; apply loop_sem.
    apply equiv_seq_eequiv with (Q' := R {{W,i,F}}); trivial.
      eapply equiv_strengthen; [ | apply equiv_assign ].
      intros k m1 m2 ((H1,H2),H3); split; [ | mem_upd_simpl ].
        rewrite (@depend_only_fv_expr (T.User Set_of_Points) (Hd F) _ m1 m2);
          [ | eapply req_mem_weaken with (2:=H1); auto with set ];
            apply (req_mem_update _ _ H1).
    apply eequiv_seq_equiv with (Q':= R {{xy,W,i,F}}); trivial.
      eapply eequiv_weaken with
        (P' := R {{W}} /-\ R {{W,i,F}})
        (Q' := (EP_eq_expr xy xy) /-\ R {{W,i,F}});
        [ | | intro; apply Rle_refl | apply Ole_refl  | ].
        intros k m1 m2 (H1,H2); repeat split; trivial;
          apply req_mem_weaken with (2:=H1); auto with set.
        intros k m1 m2 (H1,(H2,H3)); split; trivial;
          intros t v Hv; Vset_mem_inversion Hv; subst;
            [ apply H1 | | | ]; apply H2; auto with set.
      apply eequiv_inv_Modify with (M1:={{xy}}) (M2:={{xy}}) (X1:={{D,W,i,F}}) 
        (X2:={{D,W,i,F}}); trivial; try  refine (Modify_random _ _).
        intros k m1 m2 m1' m2' H1 H2 (H3,H4); split.
          intros t v Hv; Vset_mem_inversion Hv; 
            rewrite <-(H1 _ v), (H3 _ v), (H2 _ v); subst; auto with set.
          rewrite <-(H1 _ D), <-(H2 _ D); auto with set.
      apply eequiv_random_discr.  
        auto.
        intros k m1 m2 (H1,H2); expr_simpl. 
        rewrite (H1 _ W); [ | auto with set ].
        apply (pick_points_distance _ _ _ eps_pos H2).
    apply equiv_weaken with (R {{i,F}}).
      intros k m1 m2 (H1,H2); repeat split; trivial.
      unfold EP_eq_expr; expr_simpl; rewrite (H1 _ i); auto with set.
    apply equiv_inv_Modify with (M1:={{i,F}}) (M2:={{i,F}}) 
      (X1:={{D}}) (X2:={{D}}); try apply eq_refl.
      intros k m1 m2 m1' m2' H1 H2; rewrite (H1 _ D), (H2 _ D); auto with set.
      apply modify_correct with (refl1_info (empty_info E E)) Vset.empty, eq_refl.
      apply modify_correct with (refl1_info (empty_info E E)) Vset.empty, eq_refl.
    eqobs_in.
  (* Output selection *)
  apply eequiv_seq_equiv with (Q':= kreq_mem {{j,F}}); trivial.
  eapply eequiv_weaken with 
    (Q' := EP_eq_expr j j /-\ kreq_mem {{F}})
    (P' := R {{F}} /-\ kreq_mem {{F}});
    [ | | intro; apply Rle_refl | apply Ole_refl | ].
    intros k m1 m2 (H1,H2); repeat split; trivial;
      intros t v Hv; Vset_mem_inversion Hv; subst; auto with set.
    intros k m1 m2 (H1,H2) t v Hv; Vset_mem_inversion Hv; subst; auto.    
  apply eequiv_inv_Modify with (X1:={{F}}) (X2:={{F}})
    (M1:={{j}}) (M2:={{j}}); trivial; try refine (Modify_random _ _).
  apply eequiv_random_discr; [ auto | ].
    intros k m1 m2 (H1,H2); simpl; rewrite (H1 _ F);
      [ | auto with set ]; apply (pick_index_distance _ _ eps_pos H2).
  unfold Post; eqobs_in.
 Qed.

End PROOF.
