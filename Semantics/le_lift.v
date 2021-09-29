Require Import Reals.
Require Import Fourier.
Require Export DiscrProp.
Require Import Classical_Prop.

Set Implicit Arguments.

Import IUR.

 (* [<=] relation is decidable in [0,1] *)
 Parameter Uleb : U -> U -> bool.
 Parameter Uleb_spec : forall (x y: U), 
    if Uleb x y then (x <= y) else ~(x <= y). 

 Lemma Uleb_correct : forall (x y: U), 
    Uleb x y -> (x <= y).
 Proof.
  intros; generalize (Uleb_spec x y).
  rewrite H; trivial.
 Qed.

 Lemma Uleb_complete : forall (x y: U), 
   Uleb x y = false -> (y < x).
 Proof.
  intros x y.
  generalize (Uleb_spec x y). 
  case (Uleb x y).
    intros _ H; discriminate H.
    intros H _; auto.
 Qed.

 Lemma Uleb_correct_conv: forall x y : U, x <= y -> Uleb x y.
 Proof.
  intros x y H.
  generalize (Uleb_spec x y); case (Uleb x y);
    [ trivial | contradiction ].
 Qed.

 Lemma Uleb_complete_conv: forall (x y: U), y < x -> Uleb x y = false.
 Proof.
  intros x y H.
  generalize (Uleb_spec x y); case (Uleb x y);
    [ contradiction | trivial ].
 Qed.
    
 Lemma mu_stable_div_strong: forall (A:Type) (m:distr A) (k:U) f,
   f <= fcte A k -> 
   mu m (fun x : A => f x / k) == (mu m) f / k.
 Proof.
  intros.
  apply (Ueq_orc 0 k); [ auto | | ]; intros.
    rewrite (Udiv_by_zero _ H0), <-(mu_zero m).
    apply mu_stable_eq; refine (ford_eq_intro _); intro a.
     rewrite (Udiv_by_zero _ H0); trivial.
    apply mu_stable_div; trivial.
 Qed.

 Lemma sigma_Udiv: forall a f n, sigma (fun k => (f k) / a) n == (sigma f n) / a.
 Proof.
  induction n; intros.
    rewrite 2 sigma_0; auto.
    rewrite 2 sigma_S, IHn; auto.
 Qed.

 Lemma wretract_Udiv: forall f a, 
   a < 1 ->
   (forall n, sigma f n <= a) -> 
   wretract (fun k => (f k) / a).
 Proof.
  intros f a Ha Hf n.
  rewrite sigma_Udiv.
  apply Uplus_div_inv.
    rewrite <-sigma_S; apply Hf.
    apply wretract_lt.
    intros; apply Ule_lt_trans with a; auto.
 Qed.

 Lemma Udiv_one_strong: forall x, x / 1 == x.
 Proof.
  intro.
  apply (Ueq_orc 0 x); [ auto | | ]; intro H.
    rewrite <-H; auto.
    auto.
 Qed.


(** Some properties of the measure monad *)
Lemma Mswap_Mswap: forall (A B:Type) (d:Distr (A * B)), Mswap (Mswap d) == d.
Proof.
 intros A B d.
 refine (ford_eq_intro _); intro f.
 simpl.
 apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab.
 destruct ab; simpl; trivial.
Qed.

Lemma Mswap_is_Discrete_inv: forall (A B:Type) (d:Distr (A * B)), 
  is_Discrete (Mswap d) ->
  is_Discrete d.
Proof.
 intros A B d Hd.
 eapply is_Discrete_eq_compat; [ apply (Mswap_Mswap d) | ].
 apply (is_Discrete_Mlet _ Hd).
 intro; apply is_Discrete_Munit.
Qed.

Lemma Mswap_le_inv: forall (A B:Type) (d1 d2:Distr (A * B)), 
  Mswap d1 <= Mswap d2 ->
  d1 <= d2.
Proof.
 intros A B d1 d2 H.
 rewrite <-(Mswap_Mswap d1), <-(Mswap_Mswap d2).
 intro f.
 unfold Mswap at 1 3; rewrite 2 Mlet_simpl.
 apply H.
Qed.

Lemma Mswap_range: forall (A B:Type) (R: (B*A) -> Prop)  (d:Distr (A*B)), 
  range (fun ba  => R (snd ba,fst ba)) d ->
  range R (Mswap d).
Proof.
 unfold range; intros A B R d H f Hf; simpl; auto.
Qed.


Lemma mu_stable_plus_range : forall A (d:Distr A) R,
 range R d ->
 forall f g,
  (forall a, R a -> g a <= [1-] f a) ->
  mu d (fplus f g) == mu d f + mu d g.
Proof.
 intros; split.
 auto.
 transitivity (mu d (fminus (fplus f g) g) + mu d g).
 Usimpl.
 apply range_le with (1:=H).
 intros a Ha; unfold fminus, fplus.
 rewrite Uplus_minus_simpl_right; auto.
 rewrite <-(@mu_stable_plus _ d _ _); unfold fminus, fplus.
 apply range_le with (1:=H).
 intros a _; rewrite Uminus_plus_simpl; auto.
 unfold fplusok, finv; refine (ford_le_intro _); intro a.
 rewrite <-Uminus_one_left.
 apply Uminus_le_compat_left; trivial.
Qed.

Lemma mu_stable_div_eq: forall (A : Type) (m : distr A) (k : U) (f : MF A),
 (~ k == 0 ->  f <= fcte A k) ->
 (mu m) (fdiv k f) == (mu m) f / k.
Proof.
 intros.
 apply (Ueq_orc k D0); [ auto | | ]; intro Hk.
 transitivity (mu m (fzero _)).
 apply mu_stable_eq; unfold fdiv, fzero; refine (ford_eq_intro _);
  intro a; rewrite Hk; auto.
 rewrite mu_zero; auto.
 apply mu_stable_div; auto.
Qed.

(* Maybe move this to Discr_Prop.v *)
Lemma is_Discrete_distr_div: forall (A:Type) (d:Distr A) (u:U) (H: mu d (fone _) <= u),
 is_Discrete d ->
 is_Discrete (distr_div u d H).
Proof.
 intros A d u H (p,Hd).
 apply mkDiscr with p.
 intros f Hf.
 simpl; symmetry; apply Udiv_zero_eq.
 apply (Hd _ Hf).
Qed.

Lemma is_Discrete_distr_mult: forall (A:Type) (d:Distr A)  f,
 is_Discrete d ->
 is_Discrete (distr_mult f d).
Proof.
 intros A d u (p,Hd).
 apply mkDiscr with p.
 intros f Hf.
 simpl; symmetry; apply Ule_zero_eq.
 rewrite <-(mu_zero d).
 apply range_le with (1:=Hd).
 intros a Ha; unfold fzero.
 rewrite <-(Hf _ Ha); auto.
Qed.

Lemma discr_distr_simpl: forall (A:Type) (d:Distr A) (p:nat -> A) (AeqU : A -> A -O-> U),
 (forall a : A, cover (eq a) (AeqU a)) ->
 Discrete eq p d ->
 forall f, 
   serie (fun k => coeff AeqU p d k * f (p k)) ==
   serie (fun k => [1-] not_first_repr AeqU p k * (mu d (AeqU (p k)) * f (p k))).
Proof.
 intros A d p AeqU cover_uR Hd f. 
 apply serie_eq_compat; intro k.
 apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
   [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl.
   rewrite (coeff_first_repr _ cover_uR Hd _ H5); trivial.
   rewrite (coeff_not_first_repr _ _ _ _ H5); auto. 
Qed.

Lemma is_Discrete_le_compat: forall (A:Type) (d d':Distr A),
  d <= d' ->
  is_Discrete d' ->
  is_Discrete d.
Proof.
 intros A d d' Hd (p,Hp).
 apply mkDiscr with p.
 apply (enum_le Hp Hd).
Qed.
  
Lemma is_Discrete_Mlet_range: forall (A B:Type) (d:Distr A) (F:A -> Distr B) R,
  (forall a, sumbool (R a) (~R a)) ->
  range R d ->
  is_Discrete d ->
  (forall a, R a -> is_Discrete (F a)) -> 
  forall (b:B), is_Discrete (Mlet d F).
Proof.
 intros A B d F R Hdec HdR Hd HF b.
 set (F' := fun a => if Hdec a then F a else distr0 _).
 apply is_Discrete_eq_compat with (Mlet d F').
   refine (ford_eq_intro _); intro f; rewrite 2 Mlet_simpl.
   apply range_eq with (1:=HdR); intros a Ha.
   unfold F'; destruct (Hdec a) as [_ | H]; [ trivial | elim (H Ha) ].
 apply (is_Discrete_Mlet _ Hd).
 intro a; unfold F'; destruct (Hdec a); eauto using is_Discrete_distr0.
Qed.

Lemma Mlet_distr0_abs: forall (A B:Type) (F:A -> Distr B),
 Mlet (distr0 A) F == distr0 B. 
Proof.
 intros.
 apply eq_distr_intro; intro f.
 rewrite Mlet_simpl.
 trivial.
Qed.


Lemma max_comm : forall x y, max x y ==  max y x.
Proof.
 intros. 
 apply (Ule_total x y); [auto | | ]; intro H; unfold max;
  rewrite (Uminus_le_zero _ _ H), Uplus_zero_left; auto.
Qed.

   
Lemma serie_minus_le : forall f1 f2, serie f1 - serie f2 <= serie (fminus f1 f2).
Proof.
 intros.
 apply Uplus_le_perm_left.
 rewrite <-serie_plus.
 apply serie_le_compat; unfold fminus; auto.
Qed.


Lemma sigma_mult_le: forall (f:nat -> U) (c:U) (n:nat),
  c * (sigma f) n <= sigma (fun k => c * f k) n.
Proof.
 induction n.
   trivial.
   rewrite 2 sigma_S, Udistr_plus_left_le, IHn; trivial.
Qed.

Lemma serie_mult_le:
  forall (f : nat -> U) c, c * serie f <= serie (fun k => c * f k).
Proof.
 unfold serie; intros.
 apply Ole_trans with (lub (UMult c @ sigma f)); [ auto | ].
 apply lub_le_compat, fmon_le_intro; intro n.
 apply (sigma_mult_le f c n). 
Qed.

Lemma serie_lt: forall f u, 
  serie f < u ->
  forall k, f k < u.
Proof.
 intros f u H k.
 apply Ule_lt_trans with (serie f).
   unfold serie; transitivity (sigma f (S k)); 
     [ rewrite sigma_S | ]; auto.
   trivial.
Qed.

Lemma Uplus_minus_perm_assoc_eq: forall (a b c d:U), 
 c <= a ->
 d <= b ->
 a <= [1-] b ->
 c <= [1-] d ->
 a + b - (c + d) == a - c + (b - d).
Proof.
 intros; split.
 apply Uplus_minus_perm_assoc.
 apply Uplus_le_perm_right.
   apply Uinv_le_perm_right.
   rewrite H1, Uminus_plus_perm, <-Uminus_one_left, <-Uminus_assoc_right; 
     [ | | | rewrite H | rewrite Uinv_inv ]; trivial.
   transitivity (([1-]d) - c); [ rewrite Uminus_one_left; 
     apply Uminus_le_compat_left | ]; auto.
   rewrite (Uplus_sym (_ - _)), <-Uplus_assoc,
     (Uplus_assoc (a - c)), (Uminus_plus_simpl a c),
       (Uplus_sym a), Uplus_assoc, Uminus_plus_simpl; auto.
Qed.

Lemma sigma_minus_eq: forall f1 f2, 
 (forall k, f2 k <= f1 k) ->
 wretract f1 ->
 forall k,
 sigma f1 k - sigma f2 k == sigma (fun k => f1 k -  f2 k) k.
Proof.
 intros.
 induction k.
 simpl; Usimpl; auto.
 rewrite 3 sigma_S, <-IHk; unfold fminus.
 apply Uplus_minus_perm_assoc_eq; auto using (wretract_le H H0).
Qed.

Lemma serie_minus_eq : forall f1 f2, 
 (forall k, f2 k <= f1 k) ->
 wretract f1 ->
 serie f1 - serie f2 == serie (fun k => f1 k -  f2 k).
Proof.
 intros f1 f2 Hle; split.
 apply serie_minus_le.

 apply Uplus_le_perm_right.
 apply lub_lub_inv_le; intro n.
 rewrite <-sigma_minus_eq; auto.
 rewrite <-serie_plus.
 apply serie_le_compat; intros; unfold fminus; auto.
Qed.
  

Definition multRU (r:R) (u:U) : U :=
 if Rle_dec (r * iR u) 1 then 
  if Rle_dec 0 (r * iR u) then iU (r * iR u) else 0 
 else 1.

Infix "**" := multRU (at level 40).

Lemma multRU_eq_compat : forall (x y:R) (a b:U),
 x = y -> a == b -> x ** a == y ** b.
Proof.
 intros; unfold multRU.
 rewrite H.
 replace (y * iR a)%R with (y * iR b)%R by (rewrite H0; trivial).
 trivial.
Qed.

Add Parametric Morphism : multRU
 with signature @eq R ==> Oeq (O:=U) ==> Oeq (O:=U)
 as mulRU_eq_compat_r_morph.
Proof.
 intros; apply multRU_eq_compat; trivial.
Qed.

Ltac case_Rle :=
 match goal with
 |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
 end.


Lemma Rdiv_le : forall w x y z : R, 
 (0 < w)%R -> (0 < z)%R -> (x * z <= y * w)%R -> (x / w <= y / z)%R.
Proof.
 intros.
 apply Rmult_le_reg_r with w; trivial.
 apply Rmult_le_reg_r with z; trivial.
 rewrite Rdiv_mult; trivial.
 rewrite (Rmult_comm (y / z) _), Rmult_assoc.
 rewrite Rdiv_mult; trivial.
 rewrite (Rmult_comm w); trivial.
Qed.

Lemma iU_eq_inv: forall (x y:R),
  (0 <= x <= 1)%R -> 
  (0 <= y <= 1)%R -> 
  iU x == iU y -> 
  x = y.
Proof.
 intros x y H1 H2 (H3,H4).
 apply Rle_antisym; apply iU_le_inv; trivial.
Qed.


Lemma multRU_ge1 : forall (x:R) (a:U), (1 <= x)%R -> a <= x ** a.
Proof.
 intros; unfold multRU.
 repeat case_Rle.
 (* case [0,1] *)
 rewrite <-(retract_U a) at 1.
 apply iU_le.
 rewrite <-(proj2 (Rmult_ne (iR a))) at 1; auto with real.
 (* case (-inf,0) *)
 elim n; apply Rmult_le_pos; [ fourier | auto ].
 (* case (0,+inf) *)
 trivial.
Qed.
 
Lemma multRU_le_compat : forall (x y:R) (a b:U),
 (0 <= x)%R ->
 (x <= y)%R ->
 a <= b ->
 x ** a <= y ** b.
Proof.
 intros x y a b H0x Hxy Hab; unfold multRU.
 destruct (Rle_dec (x * iR a) 1) as [H1 | H1]; 
  destruct (Rle_dec 0 (x * iR a)) as [H2 | H2];
   destruct (Rle_dec (y * iR b) 1) as [H3 | H3];
    destruct (Rle_dec 0 (y * iR b)) as [H4 | H4]; trivial.
 apply iU_le; auto.
 elim H4; apply Rmult_le_pos; [ fourier | auto ].
 elim H1; rewrite <-H3; auto.
 elim H1; rewrite <-H3; auto.
 elim H1; rewrite <-H3; auto.
 elim H1; rewrite <-H3; auto.
Qed.

Lemma multRU_0_r: forall (x:R), x ** 0 == 0.
Proof.
 intros; unfold multRU.
 rewrite iR_0, Rmult_0_r.
 destruct (Rle_dec 0 1).
 destruct (Rle_dec 0 0).
 rewrite iU_0; trivial.
 trivial.
 elim n; fourier.
Qed.

Lemma multRU_1_l : forall (u:U), 1 ** u == u.
Proof.
 intros; unfold multRU.
 rewrite Rmult_1_l.
 destruct (Rle_dec (iR u) 1).
 destruct (Rle_dec 0 (iR u)).
 trivial.
 elim n; trivial.
 elim n; trivial.
Qed.

Ltac multRU_simpl :=  match goal with
   |- context [(R1 ** ?x)]   => setoid_rewrite (@multRU_1_l x) 
 | |- context [(?x **  D0)]   => setoid_rewrite (@multRU_0_r x) 
end.

Lemma multRU_spec: forall x a,
  (0 <= x)%R ->
  x ** a == iU (Rmin 1%R  (x * (iR a))%R).
Proof.
 intros.
 unfold multRU.
 destruct (Rle_dec 0 (x * iR a)) as [ _ | H' ]; [ | 
   elim H'; apply Rmult_le_pos; [fourier | auto] ].
 destruct (Rle_dec (x * iR a) 1) as [H1 | H1].
   rewrite Rmin_right; trivial.
   rewrite Rmin_left.
     symmetry; apply iU_1.
     apply (Rlt_le _ _ (Rnot_le_lt _ _ H1)).
Qed.


Lemma multRU_ge1_spec: forall (x:R) (a:U),
  (1 <= x)%R ->
  x ** a == a / iU (1/x).
Proof.
 intros.
 assert (Haux: (0 <= 1 / x <= 1)%R) by
   (split; [ apply Rdiv_pos | apply Rdiv_le_1]; fourier).
 assert (Haux':   ~ 0 == iU (1 / x)).
   rewrite <-iU_0; intro H'. 
   apply iU_eq_inv in H'; [ | split; fourier | trivial ].
   apply eq_sym in H'; destruct (Rmult_integral _ _ H').
     exfalso; fourier.
     refine (@Rinv_neq_0_compat _ (Rgt_not_eq _ _ _) H0); fourier.
 apply (Ueq_orc 0 a); [ auto | | ]; intro Ha.
   rewrite <-Ha, multRU_0_r, Udiv_zero; trivial.
 rewrite multRU_spec; [ | fourier ].
 unfold Rmin; destruct (Rle_dec 1 (x * iR a)).
   (* overflow *)
   rewrite (Udiv_le_one _ Haux'). 
   apply iU_1.
   rewrite <-(retract_U a); apply iU_le.
   replace (iR a) with (iR a / 1)%R by field.
   apply Rdiv_le; try fourier.
   rewrite Rmult_1_r, Rmult_comm; trivial.
   (* no overflow *)
   assert (Haux'': (0 <= x * iR a <= 1)%R) by (split;
     [ apply Rmult_le_pos; [fourier | auto] | apply (Rlt_le _ _ (Rnot_le_lt _ _ n)) ]).
   rewrite <-(retract_U (a / iU (1 / x))).
   apply Oeq_refl_eq; apply f_equal.
   rewrite <-(retract_R Haux'').
   apply iR_eq_morphism.
   apply (Umult_div_eq Haux').
   rewrite <-(iU_mult Haux'' Haux).
   rewrite <-(retract_U a) at 2.
   apply Oeq_refl_eq; apply f_equal.
   field; apply Rgt_not_eq; fourier.
Qed.


Lemma Umult_multRU_assoc : forall (x:R) (a b:U),
 (1 <= x)%R -> 
 (x ** a) * b <= x ** (a * b).
Proof.
 unfold multRU; intros.
 repeat case_Rle; try tauto.
 rewrite iR_mult, <-(retract_U b), <- iU_mult, retract_U, Rmult_assoc; auto.
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; rewrite iR_mult, <-Rmult_assoc, <-r.
 rewrite <-(Rmult_1_r (x * iR a)) at 2; apply Rmult_le_compat; trivial.
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; apply Rmult_le_pos; [fourier | auto].

 apply Rnot_le_lt in n.
 rewrite iR_mult, <-Rmult_assoc in *.
 apply iR_le_inv; rewrite retract_R; auto.
 rewrite iR_mult, iR_1.
 apply Rmult_le_compat; trivial; fourier.

 apply Rnot_le_lt in n.
 apply Rnot_le_lt in n0.
 rewrite iR_mult, <-Rmult_assoc in n0.
 Usimpl.
 apply iR_le_inv; rewrite iR_0.
 apply Rmult_le_reg_l with (x * iR a)%R; fourier.

 apply Rnot_le_lt in n.
 apply Rnot_le_lt in n0.
 rewrite iR_mult, <-Rmult_assoc in n0.
 Usimpl.
 apply iR_le_inv; rewrite iR_1.
 apply Rmult_le_reg_l with (x * iR a)%R.
 fourier.
 apply Rmult_le_compat; trivial; fourier.
Qed.

Lemma Umult_multRU_assoc_eq : forall (x:R) (a b:U),
 (1 <= x)%R -> 
 (x * iR a <= 1)%R ->
 (x ** a) * b == x ** (a * b).
Proof.
 unfold multRU; intros.
 repeat case_Rle; try tauto.
 rewrite iR_mult, <-(retract_U b), <- iU_mult, retract_U, Rmult_assoc; auto.
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; rewrite iR_mult, <-Rmult_assoc, <-r.
 rewrite <-(Rmult_1_r (x * iR a)) at 2; apply Rmult_le_compat; trivial.
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; apply Rmult_le_pos; [fourier | auto].
 elim n; apply Rmult_le_pos; [fourier | auto].
Qed.

Lemma Rmult_multRU_assoc : forall (x y:R) (a:U),
 (1 <= x)%R ->
 (1 <= y)%R ->  
 x ** (y ** a) == (x * y) ** a.
Proof.
 unfold multRU; split.

 (* <= *)
 destruct (Rle_dec (y * iR a) 1) as [H1 | H1];
 destruct (Rle_dec 0 (y * iR a)) as [H2 | H2];
 destruct (Rle_dec (x * y * iR a) 1) as [H3 | H3];
 destruct (Rle_dec 0 (x * y * iR a)) as [H4 | H4]; 
 trivial; try contradiction.
 
 destruct (Rle_dec (x * iR (iU (y * iR a))) 1) as [H5 | H5];
  destruct (Rle_dec 0 (x * iR (iU (y * iR a)))) as [H6 | H6].
 rewrite retract_R; auto with real.
 auto.
 elim H5; rewrite <-H3, retract_R; auto with real.
 elim H5; rewrite <-H3, retract_R; auto with real.
 
 destruct (Rle_dec (x * iR (iU (y * iR a))) 1) as [H5 | H5];
  destruct (Rle_dec 0 (x * iR (iU (y * iR a)))) as [H6 | H6]; trivial.
 elim H4; rewrite H2, Rmult_assoc, <-(proj2 (Rmult_ne (y * iR a))) at 1; 
  auto with real.
 elim H5; rewrite <-H3, retract_R; auto with real.
 elim H5; rewrite <-H3, retract_R; auto with real.
 
 rewrite iR_0, Rmult_0_r.
 destruct (Rle_dec 0 1) as [H5 | H5]; destruct (Rle_dec 0 0) as [H6 | H6].
 apply iU_le; auto.
 rewrite <-iU_0; apply iU_le; auto with real.
 elim H5; auto with real.
 elim H5; auto with real.
 
 rewrite iR_0, Rmult_0_r.
 destruct (Rle_dec 0 1) as [H5 | H5]; destruct (Rle_dec 0 0) as [H6 | H6].
 rewrite iU_0; auto.
 elim H5; auto with real.
 elim H5; auto with real.
 elim H5; auto with real.
 
 rewrite iR_1, Rmult_1_r.
 destruct (Rle_dec x 1) as [H5 | H5]; destruct (Rle_dec 0 x) as [H6 | H6].
 elim H1; rewrite <-H3, (Rle_antisym _ _ H5 H), (proj2 (Rmult_ne _)); 
  auto with real.
 rewrite <-iU_0; apply iU_le; auto with real.
 elim H1; rewrite <-H3, <-(proj2 (Rmult_ne _)), Rmult_assoc;
  apply Rmult_le_compat_r; trivial.
 elim H6; rewrite <-H;  auto with real.
 
 rewrite iR_1, Rmult_1_r.
 destruct (Rle_dec x 1) as [H5 | H5]; destruct (Rle_dec 0 x) as [H6 | H6].
 elim H4; rewrite Rmult_assoc; auto.
 auto.
 elim H4; rewrite Rmult_assoc; auto.
 elim H1; rewrite <-H3, Rmult_assoc, <-(proj2 (Rmult_ne (y * iR a))) at 1; 
  auto with real.
 
 rewrite iR_1, Rmult_1_r.
 destruct (Rle_dec x 1) as [H5 | H5]; destruct (Rle_dec 0 x) as [H6 | H6].
 elim H2; apply (@Rmult_nonnul_inv x (y * iR a));
  [ rewrite <-Rmult_assoc; trivial | fourier ].
 rewrite <-iU_0; apply iU_le; auto with real.
 elim H2; apply (@Rmult_nonnul_inv x (y * iR a));
  [ rewrite <-Rmult_assoc; trivial | fourier ].
 elim H2; apply (@Rmult_nonnul_inv x (y * iR a));
  [ rewrite <-Rmult_assoc; trivial | fourier ].
 
 rewrite iR_1, Rmult_1_r.
 destruct (Rle_dec x 1) as [H5 | H5]; destruct (Rle_dec 0 x) as [H6 | H6].
 elim H1; rewrite <-H3, (Rle_antisym _ _ H5 H), (proj2 (Rmult_ne _)); 
  auto with real.
 auto.
 elim H2; apply Rnot_le_lt in H1; fourier.
 elim H6; rewrite <-H; auto with real.

 (* => *)
 repeat case_Rle; trivial; try contradiction. 

 apply iU_le.
 rewrite retract_R; auto with real.

 elim n; transitivity (1 * iR a)%R; auto with real.

 elim n.
 apply Rle_trans with (2:=r).
 assert (W:=iR_ge_0 a).
 apply Rmult_le_compat; try fourier.
 transitivity (1 * y)%R; auto with real.
 apply Rmult_le_compat; fourier.

 elim n; apply Rmult_le_pos; [fourier | trivial].

 elim n; rewrite <-r, retract_R; auto with real.

 elim n0.
 transitivity (y * 0)%R; auto with real.
 apply Rmult_le_compat; auto with real; fourier.

 setoid_replace x with 1%R.
 rewrite Rmult_1_l; auto.
 rewrite iR_1, Rmult_1_r in r.
 auto with real.

 elim n0; apply Rmult_le_pos; [fourier | trivial].
Qed.

Lemma multRU_Umult_assoc_pair: forall (x y:R) (a b:U),
  (1 <= x)%R ->
  (1 <= y)%R ->
  (x ** a) * (y ** b) <= (x * y)%R ** (a * b).
Proof.
 intros x y a b Hx Hy.
 rewrite <-(Rmult_multRU_assoc _ Hx Hy), (Umult_sym a).
 transitivity (x ** ((y ** b) * a)).
   rewrite <-(Umult_sym a); apply (Umult_multRU_assoc _ _ Hx).
   apply multRU_le_compat; [ fourier | apply Rle_refl | ].
   apply (Umult_multRU_assoc _ _ Hy).
Qed.


Lemma multRU_distr_minus_l : forall (x:R) (a b:U),
 (1 <= x)%R ->
 x ** a - x ** b <= x ** (a - b).
Proof.
 intros x a b Hx; unfold multRU.
 repeat case_Rle;  
  try (elim n; apply Rmult_le_pos; [fourier | auto]); 
   repeat Usimpl; trivial; try tauto.

 destruct (Rle_dec (iR b) (iR a)) as [Hle | Hle].
 rewrite iR_minus, Rmult_minus_distr_l; trivial.
 apply iU_minus; trivial.
 apply Rmult_le_compat; trivial; fourier.
 
 apply Rnot_le_lt in Hle.
 rewrite Uminus_le_zero; trivial.
 apply iU_le.
 apply Rmult_le_compat; trivial; fourier.

 destruct (Rle_dec (iR b) (iR a)) as [Hle | Hle].
 rewrite iR_minus, Rmult_minus_distr_l; trivial. 
 rewrite <-iU_1.
 transitivity (iU (1 - x * iR b)).
 apply iU_minus; trivial.
 apply iU_le.
 apply Rnot_le_lt in n; fourier.

 elim n; rewrite <-r.
 apply Rnot_le_lt in Hle.
 apply Rmult_le_compat; trivial; fourier.

 elim n0; apply Rmult_le_pos; trivial; fourier.
 elim n0; apply Rmult_le_pos; trivial; fourier.
 elim n0; apply Rmult_le_pos; trivial; fourier.
Qed.

Lemma multRU_distr_minus_l_eq : forall (x:R) (a b:U),
 (1 <= x)%R ->
 (x * iR a <= 1)%R ->
 (x * iR b <= 1)%R ->
 (b <= a) ->
 x ** a - x ** b == x ** (a - b).
Proof.
 intros x a b Hx Ha Hb Hle.
 unfold multRU.
 repeat case_Rle;  
  try (elim n; apply Rmult_le_pos; [fourier | auto]); repeat Usimpl; trivial;
   try tauto.

 apply iR_le in Hle.
 rewrite iR_minus, Rmult_minus_distr_l; trivial.
 apply iU_minus; trivial.
 apply Rmult_le_compat; trivial; fourier.

 apply iR_le in Hle.
 rewrite iU_minus; trivial.
 rewrite <-Rmult_minus_distr_l; trivial.
 split; trivial.
 rewrite <-iU_1.
 apply iU_le.
 rewrite <-iR_minus; trivial.
 auto with real.
 apply Rmult_le_compat; trivial; fourier.
Qed.

Lemma multRU_distr_plus_l : forall (x:R) (a b:U),
 (1 <= x)%R ->
 x ** a + x ** b <= x ** (a + b).
Proof.
 intros; unfold multRU.
 repeat case_Rle;  
  try (elim n; apply Rmult_le_pos; [fourier | auto]); repeat Usimpl; trivial;
   try tauto.

 rewrite iR_plus.
 unfold Rmin; destruct (Rle_dec 1 (iR a + iR b)); intros.
 rewrite Rmult_1_r, (iU_ge_1 H); trivial.

 rewrite <-iU_plus; try fourier.
 apply iU_le; auto with real.

 rewrite <-Rmult_plus_distr_l.
 apply Rle_trans with (2:=r3).
 apply Rmult_le_compat; try fourier.
 assert (Ha:=iR_ge_0 a); assert (Hb:=iR_ge_0 b); fourier.
 rewrite iR_plus.
 unfold Rmin; destruct (Rle_dec 1 (iR a + iR b)); intros; trivial.
 auto with real.

 apply Rnot_le_lt in n.
 rewrite iR_plus.
 apply Rmin_case.
 rewrite Rmult_1_r, <-H, iU_1; trivial.
 rewrite Rmult_plus_distr_l.
 apply Rlt_le in n; rewrite <-n.
 rewrite <-iU_1; apply iU_le; fourier.

 elim n0; apply Rmult_le_pos; trivial; fourier.

 apply Rnot_le_lt in n.
 rewrite iR_plus.
 apply Rmin_case.
 rewrite Rmult_1_r, <-H, iU_1; trivial.
 rewrite Rmult_plus_distr_l.
 apply Rlt_le in n; rewrite <-n.
 rewrite <-iU_1; apply iU_le; fourier.

 elim n0; apply Rmult_le_pos; trivial; fourier.

 elim n0; apply Rmult_le_pos; trivial; fourier.

 elim n0; apply Rmult_le_pos; trivial; fourier.

 apply Rnot_le_lt in n.
 rewrite iR_plus.
 apply Rmin_case.
 rewrite Rmult_1_r, <-H, iU_1; trivial.
 rewrite Rmult_plus_distr_l.
 apply Rlt_le in n; rewrite <-n.
 rewrite <-iU_1; apply iU_le.
 apply Rnot_le_lt in n0; fourier.

 elim n1; apply Rmult_le_pos; trivial; fourier.
Qed.

Lemma Uplus_notoverflow: forall (x y x' y':U),
 (iR x + iR y + iR x' + iR y' <= 1)%R ->
 (Uplus x y <= [1-] (Uplus x' y'))%tord.
Proof.
 intros x y x' y' Hle.
 pose proof (iR_ge_0 x) as Hx.
 pose proof (iR_ge_0 x') as Hx'.
 pose proof (iR_ge_0 y) as Hy.
 pose proof (iR_ge_0 y') as Hy'.
 rewrite <- (retract_U (x+y)%U), <- (retract_U (x'+y')%U).
 repeat rewrite iR_plus.
 repeat (rewrite Rmin_right; [  | fourier]).
 apply iU_inv; [ | fourier].
 split; fourier.
Qed.

Lemma multRU_Rmult : forall a x,
 (1 <= a)%R -> 
 (iR (a ** x) <= a * (iR x))%R.
Proof.
 intros.
 unfold multRU.
 destruct (Rle_dec (a * iR x) 1).
 destruct (Rle_dec 0 (a * iR x)).
 rewrite retract_R; auto.
 contradict n.
 generalize (iR_ge_0 x); intros.
 apply Rmult_le_pos; auto.
 fourier.
 apply Rnot_lt_le.
 intro; contradict n; apply Rlt_le; rewrite <- iR_1; trivial.
Qed.

Lemma multRU_Rmult_b: forall a x,  
 (1 <= a)%R -> 
 (a * (iR x) <= 1)%R ->
 (iR (a ** x) = a * (iR x))%R.
Proof.
 intros.
 unfold multRU.
 destruct (Rle_dec (a * iR x) 1).
 destruct (Rle_dec 0 (a * iR x)).
 rewrite retract_R; auto.
 contradict n.
 generalize (iR_ge_0 x); intros.
 apply Rmult_le_pos; auto.
 fourier.
 contradict n; trivial.
Qed.

Lemma multRU_serie: forall (x:R) f, 
 (1 <= x)%R ->
 serie (fun k => x ** (f k)) == x ** serie f.
Proof.
 intros lam f Hlam; split.
 (* <= *) 
 apply lub_le; intro n.
 transitivity (lam ** sigma f n).
 induction n.
 simpl; auto.
 rewrite sigma_S, IHn, multRU_distr_plus_l; auto.
 apply multRU_le_compat; [ fourier | auto with real | apply le_lub ].
 (* => *)
 transitivity (UDiv (iU (1/lam)%R) (serie f));
  [  rewrite multRU_ge1_spec; trivial | ].
 transitivity (serie (fun k => f k /  iU (1/lam))); [ |
   apply serie_le_compat; intros; rewrite <-multRU_ge1_spec; trivial ] .
 rewrite (Udiv_continuous (iU (1 / lam)) (sigma f)).
 apply lub_le; intro n.
 unfold serie; rewrite <-le_lub with (n:=n).
 induction n.
   simpl; auto.
   Opaque sigma. simpl.
   rewrite 2 sigma_S, Udiv_plus; auto.
Qed.


Lemma Rmult_mu : forall (A:Type) (AeqU:A -> A -O-> U) (d:Distr A) (lam:R),
 (forall a : A, cover (eq a) (AeqU a)) ->
 is_Discrete d ->
 (1 <= lam)%R ->
 forall f,  mu d (fun a => lam ** f a) <= lam ** (mu d) f.
Proof.
 intros A AeqU d lam cover_uR Hd Hlam f.
 rewrite 2 (mu_is_Discrete _ cover_uR Hd); simpl; 
  set (p:= D_points Hd).
 rewrite <-(multRU_serie _ Hlam).
 apply serie_le_compat; intro k.
 rewrite <-(Umult_sym (f _)), <-(Umult_multRU_assoc _ _ Hlam); auto.
Qed.


Hint Resolve multRU_ge1.



Section Symm_lift.
 
(* Expression used to define the [lambda-epsilon Distance] *)
Section LE_DIST_EXPR.

 Definition d_expr A B (d1:Distr A) (d2:Distr B) (lam:R) f1 f2 :=
  (mu d1 f1 - lam ** (mu d2 f2)) + (mu d2 f2 - lam ** (mu d1 f1)).

 Lemma d_expr_le_elim : 
  forall A B (d1:Distr A) (d2:Distr B) (lam:R) (ep:U) f g,
  d_expr d1 d2 lam f g <= ep ->  
  mu d2 g - lam ** mu d1 f <= ep /\ mu d1 f - lam ** mu d2 g <= ep.
 Proof.
  unfold d_expr; intros.
  apply (Ule_total (mu d1 f) (mu d2 g)); [ auto | | ]; 
    intro H'; split; rewrite <-H; auto.
 Qed.

 Lemma d_expr_le_intro : 
  forall A B (d1:Distr A) (d2:Distr B) (lam:R) (ep:U) f g,
  (1 <= lam)%R ->
  mu d2 g - lam ** mu d1 f <= ep ->
  mu d1 f - lam ** mu d2 g <= ep ->
  d_expr d1 d2 lam f g <= ep.
 Proof.
  unfold d_expr; intros.
  apply (Ule_total (mu d1 f) (mu d2 g)); [ auto | | ]; intro H'. 
  rewrite (Uminus_le_zero (mu d1 f) (lam ** (mu d2 g))), 
   Uplus_zero_left; trivial.
  rewrite H'; auto.
  rewrite (Uminus_le_zero (mu d2 g) (lam ** mu d1 f)), 
   Uplus_zero_right; trivial.
  rewrite H'; auto.
 Qed.

 Lemma d_expr_nul : forall A (d:Distr A) (lam:R) f,
  (1 <= lam)%R -> d_expr d d lam f f == 0. 
 Proof.
  unfold d_expr; intros.
  rewrite <-(Uplus_zero_right 0).
  apply Uplus_eq_compat, Uminus_le_zero; auto.
 Qed.

 Lemma d_expr_sym : forall A B (d1:Distr A) (d2:Distr B) (lam:R) f1 f2,
  d_expr d1 d2 lam f1 f2 == d_expr d2 d1 lam f2 f1.
 Proof.
  unfold d_expr; intros; apply Uplus_sym. 
 Qed.

 Lemma d_expr_trans_aux : forall A B C (d1:Distr A) (d2:Distr B) (d3:Distr C) 
  (lam lam':R) f1 f2 f3,
  (1 <= lam)%R ->
  (1 <= lam')%R ->
  let ep  := d_expr d1 d2 lam f1 f2 in
  let ep' := d_expr d2 d3 lam' f2 f3 in 
  d_expr d1 d3 (lam * lam') f1 f3 <= 
  (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  unfold d_expr at 3.
  intros A B C d1 d2 d3 lam lam' f1 f2 f3  Hlam Hlam' ep ep'.
  apply (@Ule_total (mu d1 f1) (mu d3 f3)); [ auto | | ]; intros H.
  rewrite <-max_le_left.
  rewrite (Uminus_le_zero (mu d1 f1) ((lam * lam') ** (mu d3 f3))),
   Uplus_zero_left; [ | rewrite H; apply multRU_ge1 ].
  unfold ep, ep', d_expr.
  rewrite Uminus_triang_ineq with (c:= lam' ** (mu d2 f2)).
  apply Uplus_le_compat.
  auto.
  rewrite Rmult_comm, <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; [ | | auto]; fourier.
  rewrite <- (Rmult_1_l 1%R); apply Rmult_le_compat; try fourier; trivial.
   
  rewrite <-max_le_right.
  rewrite (Uminus_le_zero (mu d3 f3) ((lam * lam') ** (mu d1 f1))), 
   Uplus_zero_right; [ | rewrite H; apply multRU_ge1 ].
  unfold ep, ep', d_expr.
  rewrite Uminus_triang_ineq with (c:= lam ** (mu d2 f2)).
  apply Uplus_le_compat.
  auto.

  rewrite <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; [ | | auto]; fourier.
  rewrite <- (Rmult_1_l 1%R); apply Rmult_le_compat; fourier.  
 Qed.

 Lemma d_expr_trans : forall A B C (d1:Distr A) (d2:Distr B) (d3:Distr C)
  (lam lam':R) f1 f2 f3,
  (1 <= lam)%R ->
  (1 <= lam')%R ->
  let ep := d_expr d1 d2 lam f1 f2 in
  let ep' := d_expr d2 d3 lam' f2 f3 in 
  d_expr d1 d3 (lam * lam') f1 f3 <= lam' ** ep + lam ** ep'.
 Proof.
  intros.
  transitivity (max (ep + lam ** ep') (ep' + lam' ** ep)).
  apply d_expr_trans_aux; trivial.
  match goal with 
   |- (max ?A ?B) <= _ => apply (@max_eq_case  A B); [trivial | | ]; intros
  end.
  rewrite H1.
  apply Uplus_le_compat_left, multRU_ge1; trivial.
  rewrite H1, Uplus_sym.
  apply Uplus_le_compat_right, multRU_ge1; trivial.
 Qed.

 Lemma d_expr_lam_weaken : forall A B (d1: Distr A) (d2: Distr B) 
  (lam lam': R) f1 f2,
  (0 <= lam)%R ->
  (lam <= lam')%R ->
  d_expr d1 d2 lam' f1 f2 <= d_expr d1 d2 lam f1 f2.
 Proof.
  unfold d_expr; intros.
  apply Uplus_le_compat; apply Uminus_le_compat_right;
   apply multRU_le_compat; trivial.
 Qed.

 Lemma d_expr_eq_compat : forall A B (d1 d1':Distr A) (d2 d2':Distr B) 
  (lam lam':R) f1 f1' f2 f2',
   d1' == d1 ->
   d2' == d2 ->
   lam' = lam ->
   f1' == f1  ->
   f2' == f2 ->
   d_expr d1' d2' lam' f1' f2' ==  d_expr d1 d2 lam f1 f2. 
 Proof.
  unfold d_expr.
  intros A B d1 d1' d2 d2' lam lam' f1 f1' f2 f2' Hd1 Hd2 Hlam Hf1 Hf2.
  rewrite (mu_stable_eq d1' _ _ Hf1), (mu_stable_eq d2' _ _ Hf2),
    (ford_eq_elim Hd1 f1), (ford_eq_elim Hd2 f2), Hlam.
  trivial.
 Qed.

 Lemma d_expr_distr_mult : forall (A:Type) (d:Distr A) x lam f,
  (1 <= lam)%R ->
  d_expr (distr_mult (fcte A x) d) d lam f f <= [1-] (lam ** x).
 Proof.
  unfold d_expr; intros.
  simpl; unfold fcte.
  rewrite (mu_stable_mult d x f).
  rewrite (Uminus_le_zero (x * (mu d f))  (lam ** (mu d f))), 
    Uplus_zero_left; [ | rewrite Ule_mult_left; apply multRU_ge1; trivial ].
  match goal with 
   |- ?X - _ <= _ => rewrite <-(Umult_one_left X)
  end.
  rewrite <-Umult_multRU_assoc; trivial.
  rewrite <-Uminus_distr_left, Ule_mult_right; trivial.
 Qed.

 Lemma d_expr_mu_compat : forall A (AeqU:A -> A -O-> U) (d:Distr A) (lam:R),
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  forall f1 f2,
  d_expr d d lam f1 f2 <= 
  mu d (fplus (fun a => f1 a - lam ** f2 a) (fun a => f2 a - lam ** f1 a)).
 Proof.
  unfold d_expr; intros A AeqU d lam cover_uR Hd Hlam f1 f2.
  rewrite (@mu_stable_plus _ d 
   (fun a => f1 a - lam ** f2 a) (fun a => f2 a - lam ** f1 a)).
  apply Uplus_le_compat; rewrite <-mu_stable_le_minus;
   apply Uminus_le_compat_right, (Rmult_mu _ cover_uR Hd); trivial.
  intros x; unfold finv.
  apply (Ule_total (f1 x) (f2 x)); [auto| |]; intro H'.
  rewrite (Uminus_le_zero (f1 x) (lam ** (f2 x))); trivial.
  rewrite H'; apply multRU_ge1; trivial.
  rewrite (Uminus_le_zero (f2 x) (lam ** (f1 x))), Uinv_zero; auto.
  rewrite H'; apply multRU_ge1; trivial.
 Qed.

 Lemma d_expr_Mlet_right: forall (A B:Type) (d:Distr A) (F1 F2: A -> Distr B) 
   AeqU lam (ep:U),
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  forall f g,
  (forall a, Ole (d_expr (F1 a) (F2 a) lam f g) ep) ->
  Ole (d_expr (Mlet d F1) (Mlet d F2) lam  f g) ep.
 Proof.
  intros A B d F1 F2 AeqU lam ep Heq Hd Hlam f g H.
  apply d_expr_le_intro; trivial.
    rewrite 2 Mlet_simpl, <-(Rmult_mu _ Heq Hd Hlam).
    rewrite mu_stable_le_minus, <-(mu_cte_le d ep).
    apply mu_monotonic; intro a.
    apply (proj1 (d_expr_le_elim _ _ _ _ _ _ (H a))).
    rewrite 2 Mlet_simpl, <-(Rmult_mu _ Heq Hd Hlam).
    rewrite mu_stable_le_minus, <-(mu_cte_le d ep).
    apply mu_monotonic; intro a.
    apply (proj2 (d_expr_le_elim _ _ _ _ _ _ (H a))).
Qed.

End LE_DIST_EXPR.

Add Parametric Morphism A B : (@d_expr A B)
 with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> 
  (@eq R)  ==> Oeq (O:=MF A) ==> Oeq (O:=MF B) ==> Oeq (O:=U) 
 as d_expr_eq_compat_morph.
Proof.
 intros; apply d_expr_eq_compat; trivial.
Qed.


(* [Lambda-Epsilon]-Distance between two distributions *)
Section LE_DIST.

 Definition le_dist A (d1 d2:Distr A) (lam:R) (ep:U) :=
  forall f, d_expr d1 d2 lam f f <= ep.

 Lemma le_dist_nul A (d: Distr A) (lam:R):
  (1 <= lam)%R ->
  le_dist d d lam 0.
 Proof.
  unfold le_dist; intros.
  rewrite d_expr_nul; trivial.
 Qed.

 Lemma le_dist_sym A (d1 d2: Distr A) (lam:R) (ep:U) :
  le_dist d1 d2 lam ep ->
  le_dist d2 d1 lam ep.
 Proof.
  unfold le_dist; intros A d1 d2 lam ep H f.
  rewrite d_expr_sym; auto.
 Qed.

 Lemma le_dist_trans A (d1 d2 d3: Distr A) (lam lam':R) (ep ep':U) :
  (1 <= lam)%R ->
  (1 <= lam')%R ->
  le_dist d1 d2 lam ep ->
  le_dist d2 d3 lam' ep' ->
  le_dist d1 d3 (lam * lam') (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  unfold le_dist; intros A d1 d2 d3 lam lam' ep ep' Hlam Hlam' H12 H23 f.
  rewrite (d_expr_trans_aux _ d2); trivial.
  apply max_le_compat; apply Uplus_le_compat; auto using multRU_le_compat.
  apply multRU_le_compat; auto; fourier.
  apply multRU_le_compat; auto; fourier.
 Qed.

 Lemma le_dist_weaken_lam A (d1 d2:Distr A) (lam lam':R) (ep:U) :
  (0 <= lam' <= lam)%R ->
  le_dist d1 d2 lam' ep ->
  le_dist d1 d2 lam ep.
 Proof.
  unfold le_dist; intros A d1 d2 lam lam' ep (?,?) Hf f.
  rewrite <-(Hf f); apply d_expr_lam_weaken; auto.
 Qed.

 Lemma le_dist_weaken_ep A (d1 d2:Distr A) (lam:R) (ep ep':U) :
  ep' <= ep ->
  le_dist d1 d2 lam ep' ->
  le_dist d1 d2 lam ep.
 Proof.
  unfold le_dist; intros.
  transitivity ep'; auto.
 Qed.

 Lemma le_dist_weaken A (d1 d2:Distr A) (lam lam':R) (ep ep':U) :
  ep' <= ep ->
  (0 <= lam' <= lam)%R ->
  le_dist d1 d2 lam' ep' ->
  le_dist d1 d2 lam ep.
 Proof.
  intros.
  apply le_dist_weaken_ep with ep'; trivial.
  apply le_dist_weaken_lam with lam'; trivial.
 Qed.    

 Lemma le_dist_D1_0 : forall A (d1 d2:Distr A),
  le_dist d1 d2 R1 0 -> d1 == d2.
 Proof.
  unfold le_dist, d_expr; intros.
  refine (ford_eq_intro _); intro f.
  rewrite <-Uabs_diff_zero; apply Ule_zero_eq.
  rewrite <-(H f), multRU_1_l, multRU_1_l; trivial.
 Qed.

 Lemma le_dist_Mlet : forall A B (d1 d2:Distr A) (F:A->Distr B) (lam:R) (ep:U),
  le_dist d1 d2 lam ep ->
  le_dist (Mlet d1 F) (Mlet d2 F) lam ep.
 Proof.
  unfold le_dist, d_expr; intros.
  repeat rewrite Mlet_simpl.
  apply H.
 Qed.

 Lemma le_dist_Mlet_right: forall (A B:Type) (d:Distr A) (F1 F2: A -> Distr B) 
   AeqU lam ep,
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  (forall a, le_dist (F1 a) (F2 a) lam ep) ->
  le_dist (Mlet d F1) (Mlet d F2) lam ep.
 Proof.
   unfold le_dist; intros A B d F1 F2 AeqU lam ep Heq Hd Hlam H f.
   apply d_expr_Mlet_right with AeqU; auto.
 Qed.


Section DIST_DISCR_BOUND.

Section Asym_bound.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Variable lam:R.

 Hypothesis Hlam: (1 <= lam)%R.

 Variable p: nat -> A.
 Hypothesis d1_discr : Discrete (@eq A) p d1.
 Hypothesis d2_discr : Discrete (@eq A) p d2.

 Let P : A -> boolO := 
   fun a => Uleb (lam ** mu d2 (AeqU a)) (mu d1 (AeqU a)).

 Lemma d_expr_restr_le:forall f,
   mu d1 f - lam ** (mu d2 f) <=  mu d1 (restr P f) - lam ** (mu d2 (restr P f)).
 Proof.
  intros.
  rewrite (mu_restr_split d1 P f), (mu_restr_split d2 P f).
  rewrite <-(multRU_distr_plus_l _ _ Hlam).
  rewrite Uplus_minus_perm_assoc, (Uminus_le_zero (mu d1 (restr (negP P) f))),
    Uplus_zero_right; trivial.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <-(multRU_serie _ Hlam).
  apply serie_le_compat; intro.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
    rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
      (coeff_first_repr _ cover_uR d2_discr _ H5).
    unfold restr, negP, negb, P.
    case_eq (Uleb (lam ** (mu d2) (AeqU (p k))) ((mu d1) (AeqU (p k)))); intro Heq.
      rewrite 2 Umult_zero_right; trivial.
      pose proof (Ult_le (Uleb_complete Heq)).
      rewrite <-(Umult_multRU_assoc _ _ Hlam).
      apply Umult_le_compat_left; apply (Ult_le (Uleb_complete Heq)).
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
 Qed.

 Lemma d_expr_restr_fone:forall f,
   mu d1 (restr P f) - lam ** (mu d2 (restr P f)) <=
   mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _))).
 Proof.
  intros.
  rewrite 2 (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    2 (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <- 2 (multRU_serie _ Hlam).
  rewrite serie_minus_le, serie_minus_eq; unfold fminus.
    (* 1st subgoal *)
    apply serie_le_compat; intros k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        rewrite 2 Umult_one_right, <-(Umult_multRU_assoc _ _ Hlam), 
          <-Uminus_distr_left; auto.
        repeat Usimpl; trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
    (* 2nd subgoal *)
    intro k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H;
        try (repeat (Usimpl || multRU_simpl)); trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); Usimpl; multRU_simpl; trivial.
    (* 3rd subgoal *)
    apply wretract_le with (2:=wretract_coeff _ cover_uR p d1);
     intro; auto.
 Qed.

 Lemma d_expr_restr_serie:forall f,
   mu d1 (restr P f) - lam ** (mu d2 (restr P f)) <=
   serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)).
 Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <-(multRU_serie _ Hlam).
  rewrite serie_minus_le; unfold fminus.
  apply serie_le_compat; intro k.
  rewrite <-(Umult_multRU_assoc _ _ Hlam), <-Uminus_distr_left; trivial.
 Qed.

 Lemma d_expr_restr_serie_inv:
  serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) <= 
  mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _))).
 Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  transitivity  (serie (fun k => coeff AeqU p d1 k * restr P (fone A) (p k) - 
    (lam ** ((coeff AeqU p d2 k) * restr P (fone A) (p k))))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        repeat Usimpl; trivial.
        rewrite (Uminus_le_zero _ _ (Ult_le H)); trivial.
      (* not first repr *)
        rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
  rewrite <-(multRU_serie _ Hlam).
  rewrite serie_minus_eq; trivial.
    intros k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        repeat Usimpl; trivial.
        Usimpl; multRU_simpl; trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); Usimpl; multRU_simpl; trivial.
   apply wretract_le with (2:=wretract_coeff _ cover_uR p d1);
     intro; auto.
 Qed.

End Asym_bound.


(* Characterization of the [lam-eps] distance for discrete distributions *)
Section CHARACTERIZATION.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Variable lam:R.

 Hypothesis Hlam: (1 <= lam)%R.

 Variable p: nat -> A.
 Hypothesis d1_discr : Discrete (@eq A) p d1.
 Hypothesis d2_discr : Discrete (@eq A) p d2.


 Let Pl : A -> boolO := 
   fun a => Uleb (lam ** mu d2 (AeqU a)) (mu d1 (AeqU a)).
 Let Pr : A -> boolO := 
   fun a => Uleb (lam ** mu d1 (AeqU a)) (mu d2 (AeqU a)).

 Lemma le_dist_discr_ub: 
   let epl :=  mu d1 (restr Pl (fone _)) - lam ** (mu d2 (restr Pl (fone _))) in
   let epr :=  mu d2 (restr Pr (fone _)) - lam ** (mu d1 (restr Pr (fone _))) in
   le_dist d1 d2 lam (max epl epr).
 Proof.
  intros epl epr f.
  apply (d_expr_le_intro _ _ _ _ _ Hlam).
    rewrite (d_expr_restr_le _ cover_uR Hlam d2_discr d1_discr f), <-max_le_left. 
    apply d_expr_restr_fone with p; trivial.
    rewrite (d_expr_restr_le _ cover_uR Hlam d1_discr d2_discr f), <-max_le_right.
    apply d_expr_restr_fone with p; trivial.
 Qed.

 Lemma le_dist_discr_intro: forall ep,
   mu d1 (restr Pl (fone _)) - lam ** (mu d2 (restr Pl (fone _))) <= ep -> 
   mu d2 (restr Pr (fone _)) - lam ** (mu d1 (restr Pr (fone _))) <= ep -> 
   le_dist d1 d2 lam ep.
 Proof.
  intros.
  eapply le_dist_weaken with (lam':=lam); [ | | apply le_dist_discr_ub ].
  apply max_le; trivial.
  split; fourier.
 Qed.


 Lemma le_dist_discr_lb: forall ep, 
   le_dist d1 d2 lam ep ->
   let epl :=  mu d1 (restr Pl (fone _)) - lam ** (mu d2 (restr Pl (fone _))) in
   let epr :=  mu d2 (restr Pr (fone _)) - lam ** (mu d1 (restr Pr (fone _))) in
   (max epl epr) <= ep.
 Proof.
  intros ep H epl epr.
  apply max_le.
    destruct (d_expr_le_elim _ _ _ _ _ _ (H (restr Pl (fone A)))); trivial.
    destruct (d_expr_le_elim _ _ _ _ _ _ (H (restr Pr (fone A)))); trivial.
 Qed.

 Lemma le_dist_discr_ub_serie: 
   let epl := serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) in
   let epr := serie (fun k => coeff AeqU p d2 k - lam ** (coeff AeqU p d1 k)) in
   le_dist d1 d2 lam (max epl epr).
 Proof.
  intros epl epr f.
  rewrite le_dist_discr_ub.
  apply max_le_compat; apply (d_expr_restr_serie _ cover_uR Hlam); trivial.
 Qed.

 Lemma le_dist_discr_serie_intro: forall ep,
   serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) <= ep -> 
   serie (fun k => coeff AeqU p d2 k - lam ** (coeff AeqU p d1 k)) <= ep ->
   le_dist d1 d2 lam ep.
 Proof.
  intros.
  eapply le_dist_weaken with (lam':=lam); [ | | apply le_dist_discr_ub_serie ].
  apply max_le; trivial.
  split; fourier.
 Qed.

 Lemma le_dist_discr_lb_serie: forall ep, 
   le_dist d1 d2 lam ep ->
   let epl := serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) in
   let epr := serie (fun k => coeff AeqU p d2 k - lam ** (coeff AeqU p d1 k)) in
   (max epl epr) <= ep.
 Proof.
  intros ep H epl epr.
  rewrite <-(le_dist_discr_lb H).
  apply max_le_compat; apply (d_expr_restr_serie_inv _ cover_uR Hlam); trivial.
 Qed.

End CHARACTERIZATION.


(* Some specializations of the previous rules *)
Section SPECIALIZATION.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Variable lam:R.

 Hypothesis Hlam: (1 <= lam)%R.

 Variable p: nat -> A.
 Hypothesis d1_discr : Discrete (@eq A) p d1.
 Hypothesis d2_discr : Discrete (@eq A) p d2.

 Let Pl : A -> boolO := 
   fun a => Uleb (lam ** mu d2 (AeqU a)) (mu d1 (AeqU a)).
 Let Pr : A -> boolO := 
   fun a => Uleb (lam ** mu d1 (AeqU a)) (mu d2 (AeqU a)).

 Lemma le_dist_discr_ub_le: 
   d1 <= d2 ->
   let epr :=  mu d2 (restr Pr (fone _)) - lam ** (mu d1 (restr Pr (fone _))) in
   le_dist d1 d2 lam epr.
 Proof.
  intros Hd epr f.
  rewrite (le_dist_discr_ub _ cover_uR Hlam (enum_le d2_discr Hd) d2_discr f).
  apply max_eq_left.
  rewrite Uminus_le_zero; trivial.
  rewrite <-multRU_1_l.
  refine (multRU_le_compat _ _ _ Hlam _); auto with real.
 Qed.

 Lemma le_dist_discr_ub_le_serie: 
   d1 <= d2 ->
   let epr := serie (fun k => coeff AeqU p d2 k - lam ** (coeff AeqU p d1 k)) in
   le_dist d1 d2 lam epr.
 Proof.
  intros Hd epr f.
  rewrite (le_dist_discr_ub_le Hd f).
  apply (d_expr_restr_serie _ cover_uR Hlam d2_discr (enum_le d2_discr Hd)).
 Qed.

 Lemma le_dist_discr_lb_le_serie: forall ep, 
   d1 <= d2 ->
   le_dist d1 d2 lam ep ->
   let epr := serie (fun k => coeff AeqU p d2 k - lam ** (coeff AeqU p d1 k)) in
   epr <= ep.
 Proof.
  intros ep Hd H epr.
  rewrite <-(le_dist_discr_lb_serie _ cover_uR Hlam (enum_le d2_discr Hd) d2_discr H).
  rewrite max_eq_left; trivial.
  apply Ole_trans with 0; trivial.
  apply serie_zero; intro k; apply Uminus_le_zero.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
    (* first repr *)
    rewrite (coeff_first_repr _ cover_uR (enum_le d2_discr Hd) _ H5),
      (coeff_first_repr _ cover_uR d2_discr _ H5).
    rewrite <-(multRU_1_l (mu d1 (AeqU (p k))));
    apply multRU_le_compat; [ fourier | apply Hlam | apply Hd ].
    (* not first repr *)
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
 Qed.

 Lemma le_dist_discr_lb_le: forall ep, 
   d1 <= d2 ->
   le_dist d1 d2 lam ep ->
   let epr :=  mu d2 (restr Pr (fone _)) - lam ** (mu d1 (restr Pr (fone _))) in
   epr <= ep.
 Proof.
  intros ep Hd H epr.
  rewrite <-(le_dist_discr_lb_le_serie Hd H).
  unfold epr.
  apply (d_expr_restr_serie _ cover_uR Hlam d2_discr (enum_le d2_discr Hd)). 
 Qed.

 Lemma le_dist_discr_pointwise_ub: forall (F G:A -> U),
  (forall (a:A), mu d1 (AeqU a) - lam ** (mu d2 (AeqU a)) <= F a) ->
  (forall (a:A), mu d2 (AeqU a) - lam ** (mu d1 (AeqU a)) <= G a) ->
  let epl := serie (fun k => F (p k)) in
  let epr := serie (fun k => G (p k)) in
  le_dist d1 d2 lam (max epl epr).
 Proof.
  intros F G HF HG epl epr.
  eapply le_dist_weaken with (lam':=lam); [ | split; fourier |  
    apply (le_dist_discr_ub_serie _ cover_uR Hlam d1_discr d2_discr) ].
  apply max_le_compat; [ unfold epl | unfold epr ].
    (*  *)
    apply serie_le_compat; intro k.
    rewrite <-HF.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
      [auto | | ]; intros [H4 H5].
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5); trivial.
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
    (*  *)
    apply serie_le_compat; intro k.
    rewrite <-HG.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
      [auto | | ]; intros [H4 H5].
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5); trivial.
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
 Qed.


End SPECIALIZATION.

End DIST_DISCR_BOUND.


Section LE_DIST_MLET_DISCR.

Lemma wretract_prod_eq_proj1: forall (A B:Type) (d:Distr B) (carA:A -> MF A) (carB:B -> MF B) 
  (p:nat -> (A*B)),
 (forall a, cover (fun x => a = x) (carA a)) ->
 (forall b, cover (fun x => b = x) (carB b)) ->
 forall a,
 wretract (fun k => [1-] not_first_repr (carProd carA carB) p k * carA (fst (p k)) a *
  mu d (carB (snd (p k)))).
Proof.
 intros A B d carA carB p carA_prop carB_prop a k.
 pose proof (carProd_prop _ _ carA_prop carB_prop) as carAB_prop;
 set (carAB := carProd carA carB); fold carAB in carAB_prop.
 apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
    [auto | | ]; intros [H4 H5]; rewrite H5; repeat Usimpl.
     (* case [first repr k of (p k) == 1] *)
     transitivity ([1-] (sigma (fun k => mu d 
       (fmult ([1-] not_first_repr carAB p k) (fun b => carAB (p k) (a,b)))) k));
     [ | apply Uinv_le_compat, sigma_le_compat; intros; rewrite <-(mu_stable_mult d (_ * _));
       apply mu_monotonic; unfold fmult; intro b; apply Umult_assoc ].
     (* Push the [sigma] inside the function measured by d1 *)
     rewrite <-mu_sigma_eq.
     Focus 2.
     intros b k' Hk'; unfold fmult.
     apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k'); 
     [auto | | ]; intros [_ H5'].
       (* case [first repr k' of (p k') == 1] *) 
       rewrite H5'; repeat Usimpl.
       apply (cover_elim (carAB_prop (p k')) (a,b)); [auto | | ]; intros [H1 H2]. 
         rewrite H2; trivial.
         rewrite H2, sigma_zero; [auto | ].
         intros k'' Hk''.
         apply Umult_zero_right_eq.
         rewrite <-H1, (carA_sym _ carAB_prop).
         apply (@sigma_zero_elim (fun i => carAB (p k') (p i)) k'); trivial.
       (* case [first repr k' of (p k') == 1] *) 
       rewrite H5'; repeat Usimpl; trivial.
     (* Conclude the proof *) 
     rewrite <-(mu_stable_mult d (carA (fst (p k)) a)).
     apply mu_fplusok; intro b; unfold finv, sigma_fun, fmult.
     match goal with |- _ <= ?X => change (carAB (p k) (a,b) <= X) end.
     apply (cover_elim (carAB_prop (p k)) (a,b)); [auto | | ]; intros [? Heq].
       rewrite Heq; trivial.
       rewrite Heq, sigma_zero; [auto | ].
       intros k' Hk'.
       apply Umult_zero_right_eq.
       rewrite <-H, (carA_sym _ carAB_prop).
       apply (@sigma_zero_elim (fun i => carAB (p k) (p i)) k); trivial.

     (* case [first repr k of (p k) == 1] *)
     trivial.
 Qed.

(*
(* Sufficient condition for proving hypothesis [d1'_discr]
   and [d2'_discr] in the following section *)
Section Discr_aux.

 Variable A B: Type.
 Variable d: Distr A.
 Variable F:A -> Distr B.

 Variable pa: nat -> A.
 Variable pb: A -> nat -> B.

 Hypothesis d_discr: Discrete eq pa d.
 Hypothesis F_discr: forall a : A, Discrete eq (pb a) (F a).

 Let d':= Mlet d (fun a => prod_distr (Munit a) (F a)).

 Let pa' : A -> nat -> A*B :=
   fun a k => let (i, j) := bij_n_nxn k in (fun b k' => (a,b)) (pb a i) j.

 Let  p := (fun k : nat => let (i, j) := bij_n_nxn k in pa' (pa i) j).

 Lemma d'_discr: Discrete eq p d'.
 Proof. 
   apply (enum_Mlet _ _ d_discr).  
   unfold prod_distr, pa'; intro.
   rewrite (proj1 (Mlet_unit a (fun x => Mlet (F a) (fun b => Munit (x, b))))).
   apply (@enum_Mlet _ _ (F a) (fun b : B => Munit (a, b)) (pb a)
   (fun b k => (a,b)) (@F_discr a)).
   intro a'; apply enum_Munit.
   apply exc_intro with (0%nat); trivial.
 Qed.

End Discr_aux.
*)


  Variable A B: Type.
  Variable d1 d2: Distr A.
  Variable F1 F2:A -> Distr B.

  Variable lam lam':R.
  Variable ep ep':U.
  Hypothesis Hlam  : (1 <= lam)%R.
  Hypothesis Hlam' : (1 <= lam')%R.
 
  Variable carA: A -> A -O-> U.
  Variable carB: B -> B -O-> U.

  Hypothesis carA_prop:  forall a:A , cover (eq a) (carA a).
  Hypothesis carB_prop:  forall b:B , cover (eq b) (carB b).

  Let carAB: A*B -> MF (A*B) := carProd carA carB.
  Lemma carAB_prop: forall ab, cover (fun x => ab = x) (carAB ab). 
  Proof.
   apply (carProd_prop _ _ carA_prop carB_prop).
  Qed.

  Let d1' := Mlet d1 (fun a : A => prod_distr (Munit a) (F1 a)).
  Let d2' := Mlet d2 (fun a : A => prod_distr (Munit a) (F2 a)).

  Variable d1'_discr: is_Discrete d1'.
  Variable d2'_discr: is_Discrete d2'.

  Let p := (parity_split (D_points d1'_discr) (D_points d2'_discr)).

  Let p1 := fun k => fst (p k).
  Let p2 := fun k => snd (p k).

  Let Fl:= fun ab => restr (fun ab' => Uleb
    ((lam * lam') ** mu d2 (fun a => mu (F2 a) (fun b => carAB ab' (a,b))))
    (mu d1 (fun a => mu (F1 a) (fun b => carAB ab' (a,b))))) (fone (A * B)) ab.
  Let Fr:= fun ab => restr (fun ab' => Uleb
    ((lam * lam') ** mu d1 (fun a => mu (F1 a) (fun b => carAB ab' (a,b))))
    (mu d2 (fun a => mu (F2 a) (fun b => carAB ab' (a,b))))) (fone (A * B)) ab.
  Let Ml := fun (a:A) (k:nat) (b:B) => carB (p2 k) b * 
    [1-] not_first_repr carAB p k * carA (p1 k) a * Fl (a, p2 k).
  Let Mr := fun (a:A) (k:nat) (b:B) => carB (p2 k) b * 
    [1-] not_first_repr carAB p k * carA (p1 k) a *  Fr (a, p2 k).
  Let Ml' := fun (k:nat) (a:A) =>  [1-] not_first_repr carA p1 k *  
     carA (p1 k) a * (lam' ** mu (F2 (p1 k)) (serie_fun (Ml (p1 k)))).
  Let Mr' := fun (k:nat) (a:A) =>  [1-] not_first_repr carA p1 k *  
     carA (p1 k) a * (lam' ** mu (F1 (p1 k)) (serie_fun (Mr (p1 k)))).


 Lemma le_dist_Mlet_prod_discr: forall S,
   range S d1 ->
   range S d2 ->
   le_dist d1 d2 lam ep -> 
   (forall a, S a -> le_dist (F1 a) (F2 a) lam' ep') -> 
   le_dist d1' d2' (lam * lam') (ep + ep').
 Proof.
  intros S HSd1 HSd2 Hd HF.
  assert (Hlamlam': (1<=lam * lam')%R) by
    (rewrite <-Rmult_1_l at 1; apply Rmult_le_compat; fourier).
  apply (le_dist_discr_intro _ carAB_prop Hlamlam' 
    (disc_eqpoint_l d1'_discr d2'_discr)
    (disc_eqpoint_r d1'_discr d2'_discr)).
  (* Left ineq *)
  (* Discretize *)
  rewrite (mu_is_Discrete _ carAB_prop 
    (mkDiscr  (disc_eqpoint_l d1'_discr d2'_discr))),
    (mu_is_Discrete _ carAB_prop 
      (mkDiscr (disc_eqpoint_r d1'_discr d2'_discr))); simpl.
  rewrite  (discr_distr_simpl _ carAB_prop  (disc_eqpoint_l d1'_discr d2'_discr)),
    (discr_distr_simpl _ carAB_prop  (disc_eqpoint_r d1'_discr d2'_discr)).
  change (serie (fun k => 
    [1-] not_first_repr carAB p k * (mu d1' (carAB (p k)) * Fl (p k))) -
    (lam * lam') ** serie (fun k => [1-] not_first_repr carAB p k *
      (mu d2' (carAB (p k)) * Fl (p k))) <= ep + ep').
  (* Simplify [d1'] and [d2'] *)
  transitivity (serie 
    (fun k => [1-] not_first_repr carAB p k * (mu d1 (carA (p1 k)) *
      (mu (F1 (p1 k)) (carB (p2 k)) * Fl (p k)))) -
     (lam * lam') ** serie
    (fun k => [1-] not_first_repr carAB p k * (mu d2 (carA (p1 k)) *
      (mu (F2 (p1 k)) (carB (p2 k)) * Fl (p k))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro k; Usimpl.
    simpl; rewrite Umult_assoc; Usimpl.
    rewrite <-(mu_stable_mult_right d1).
    apply (mu_monotonic d1); refine (ford_le_intro _); intro a'.
    apply (cover_elim (carA_prop (p1 k)) a'); [ auto | | ]; intros [H4 H5];
      rewrite H5; Usimpl.
      rewrite <-(mu_zero (F1 a')); apply (mu_monotonic (F1 a')); intro b';
        unfold carAB, carProd, fzero; simpl; unfold p1 in H5; rewrite H5; trivial.
      rewrite H4; apply (mu_monotonic (F1 a')); intro b';
        unfold carAB, carProd; simpl; trivial.
    (* right term *)
    apply multRU_le_compat; [ apply Rmult_le_pos; fourier | apply Rle_refl | ].
    apply serie_le_compat; intro k; Usimpl.
    simpl; rewrite Umult_assoc; Usimpl.
    rewrite <-(mu_stable_mult_right d2).
    apply (mu_monotonic d2); refine (ford_le_intro _); intro a'.
    apply (cover_elim (carA_prop (p1 k)) a'); [ auto | | ]; intros [H4 H5];
      rewrite H5; Usimpl.
      rewrite <-(mu_zero (F2 a')); apply (mu_monotonic (F2 a')); intro b';
        unfold carAB, carProd, fzero; simpl; unfold p1 in H5; rewrite H5; trivial.
      rewrite H4; apply (mu_monotonic (F2 a')); intro b';
        unfold carAB, carProd; simpl; unfold p1 in H5; rewrite H5; auto.
  (* Write the sum over a pair as two nested sums and
     factorize some terms*)
  unfold carAB, p1, p2.
  rewrite (sigma_prod_split_r _ _ p carA_prop carB_prop
    (fun ab => mu d1 (carA (fst ab)) * (mu (F1 (fst ab)) 
      (carB (snd ab)) * Fl ab))),
    (sigma_prod_split_r _ _ p carA_prop carB_prop
      (fun ab => mu d2 (carA (fst ab)) * (mu (F2 (fst ab)) 
        (carB (snd ab)) * Fl ab))); simpl.
  transitivity (serie (fun ka =>
    [1-] not_first_repr carA (fun k => fst (p k)) ka *
    mu d1 (carA (fst (p ka))) *
    serie (fun kb =>
       [1-] not_first_repr carAB p kb *
       carA (fst (p kb)) (fst (p ka)) *
       (mu (F1 (fst (p ka))) (carB (snd (p kb))) *
         Fl (fst (p ka), snd (p kb))))) -
    (lam * lam') ** serie (fun ka =>
      [1-] not_first_repr carA (fun k => fst (p k)) ka *
      serie (fun kb =>
        [1-] not_first_repr carAB p kb *
        carA (fst (p kb)) (fst (p ka)) *
        (mu d2 (carA (fst (p ka))) *
          (mu (F2 (fst (p ka))) (carB (snd (p kb))) *
           Fl (fst (p ka), snd (p kb))))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro k.
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-serie_mult.
    apply serie_le_compat; intro kb; auto.
    apply wretract_le with (fun kb => [1-] not_first_repr carAB p kb *
      carA (p1 kb) (fst (p k)) * mu (F1 (fst (p k))) (carB (p2 kb))); [ auto | ].
    apply (wretract_prod_eq_proj1 _ _ _ _ carA_prop carB_prop).
    (* right term *)
    apply multRU_le_compat; [ apply Rmult_le_pos; fourier | apply Rle_refl | ].
    apply serie_le_compat; intro ka; Usimpl.
    apply serie_le_compat; intro kb; auto.
  (* Push [lam'] inside the serie *)
  rewrite Uminus_le_compat_right with (y:= lam ** serie
     (fun ka =>
      [1-] not_first_repr carA p1 ka *
      mu d2 (carA (p1 ka)) * (lam' **
      serie (fun kb => [1-] not_first_repr carAB p kb * 
        carA (fst (p kb)) (fst (p ka)) *
         (mu (F2 (fst (p ka))) (carB (snd (p kb))) *
            Fl (fst (p ka), snd (p kb))))))).
  Focus 2.
  unfold p1, p2.
  rewrite <-(Rmult_multRU_assoc _ Hlam Hlam').
  apply multRU_le_compat; [ fourier | apply Rle_refl | ].
  rewrite <-(multRU_serie _ Hlam').
  apply serie_le_compat; intro ka.
  rewrite (Umult_sym ([1-] _) (serie _)), <-(Umult_multRU_assoc _ _ Hlam'),
   <-Umult_assoc, (Umult_sym (_ ** _)); Usimpl.
  rewrite Umult_sym, (Umult_multRU_assoc _ _ Hlam').
  apply multRU_le_compat; [ fourier | apply Rle_refl | ].
  rewrite Umult_sym, serie_mult_le.
  apply serie_le_compat; intro kb; auto.
  (* Push both inner series inside the functions measured by
     distributions [F1 (p1 ka)] and  [F2 (p1 ka)] respectively *) 
  transitivity (
    serie  (fun ka => [1-] not_first_repr carA p1 ka *
      mu d1 (carA (p1 ka)) * mu (F1 (p1 ka)) (serie_fun (Ml (p1 ka)))) -
    lam ** serie (fun ka => [1-] not_first_repr carA p1 ka *
      mu d2 (carA (p1 ka)) * (lam' **
        mu (F2 (p1 ka)) (serie_fun (Ml (p1 ka)))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro ka.
    apply Umult_le_compat_right.
    rewrite mu_serie_eq.
    apply serie_le_compat; intro kb.
    unfold Ml.
    rewrite (Umult_sym), <-Umult_assoc, <-mu_stable_mult_right.
    apply mu_monotonic; intro b.
    rewrite <-(Umult_assoc (carB _ _)), <-(Umult_assoc _ (_ * _)); 
      apply Umult_le_compat_right; auto.
    intros b; unfold Ml.
    apply wretract_le with (fun k => [1-] not_first_repr carAB p k * carAB (p k) (fst (p ka),b)).
      intros k.
      rewrite Ule_mult_right, <-Umult_sym.
      unfold carAB at 3, carProd; simpl; auto.
    apply (enum_wretract_eq _ _ carAB_prop).
    (* right term *)
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    apply serie_le_compat; intro ka.
    apply Umult_le_compat_right.
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    rewrite mu_serie_le. 
    apply serie_le_compat; intro kb.
    unfold Ml.
    rewrite (Umult_sym), <-Umult_assoc, <-mu_stable_mult_right.
    apply mu_monotonic; intro b.
    rewrite <-(Umult_assoc (carB _ _)), <-(Umult_assoc _ (_ * _)); 
      apply Umult_le_compat_right; auto.
  (* Transitivity with .... and bound the left-most term by [ep'] *)
  rewrite Uminus_triang_ineq with (c:= serie (fun ka =>
      [1-] not_first_repr carA p1 ka * mu d1 (carA (p1 ka)) *
      (lam' ** mu (F2 (p1 ka)) (serie_fun (Ml (p1 ka)))))).
  rewrite (Uplus_sym ep); apply Uplus_le_compat.
    transitivity (serie (fun ka => ep' * 
      ([1-] not_first_repr carA p1 ka * mu d1 (carA (p1 ka))))).
      rewrite serie_minus_le; unfold fminus.
      apply serie_le_compat; intro ka.
      rewrite <-(mu_stable_mult d1 ([1-] _)), <- 2 (mu_stable_mult_right d1),
       <-(mu_stable_mult d1 ep'), mu_stable_le_minus.
      apply range_le with (1:=HSd1).
        intros a Ha; unfold fmult.
        apply (cover_elim (carA_prop (p1 ka)) a); [auto | | ]; intros [H1 H2];
          rewrite H2; repeat Usimpl; trivial.
          rewrite H1.
          rewrite <-Uminus_distr_right; Usimpl.
          apply (d_expr_le_elim _ _ _ _ _ _ (HF _ Ha (serie_fun (Ml a)))).
        rewrite (serie_mult _ (enum_wretact_mu d1 _ p1 carA_prop)); trivial.
  (* Push term [lam' ** mu (F2 (p1 ka)) (serie_fun (M (p1 ka)))] inside 
     the functions measured by distributions [d1] and [d2] *)
  transitivity (mu d1 (serie_fun Ml') - lam ** mu d2 (serie_fun Ml')).
    apply Uminus_le_compat.
    (* left term *)
    rewrite mu_serie_eq. 
    apply serie_le_compat; intro ka; unfold Ml'.
    rewrite <-(mu_stable_mult d1 ([1-] not_first_repr carA p1 ka)),
      <-(mu_stable_mult_right d1).
    apply mu_monotonic; intro a; unfold fmult; auto.
    intro a; unfold Ml'.
    apply wretract_le with (fun k => [1-] not_first_repr carA p1 k *
       carA (p1 k) a); [ auto | ].
    apply (enum_wretract_eq _ _ carA_prop).
    (* right term *) 
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    rewrite mu_serie_le.
    apply serie_le_compat; intro ka; unfold Ml'.
    rewrite <-(mu_stable_mult d2 ([1-] not_first_repr carA p1 ka)),
       <-(mu_stable_mult_right d2).
     apply mu_monotonic; intro a; unfold fmult; auto.
  (* Apply hypothesis regarding the distance between [d1] and 
     [d2] to conclude *)
  apply (d_expr_le_elim _ _ _ _ _ _ (Hd (serie_fun Ml'))).

  (* Right ineq *)
  (* Discretize *)
  rewrite (mu_is_Discrete _ carAB_prop 
    (mkDiscr  (disc_eqpoint_l d1'_discr d2'_discr))),
    (mu_is_Discrete _ carAB_prop 
      (mkDiscr  (disc_eqpoint_r d1'_discr d2'_discr))); simpl.
  rewrite  (discr_distr_simpl _ carAB_prop 
    (disc_eqpoint_l d1'_discr d2'_discr)),
    (discr_distr_simpl _ carAB_prop 
    (disc_eqpoint_r d1'_discr d2'_discr)).
  change (serie (fun k => 
    [1-] not_first_repr carAB p k * (mu d2' (carAB (p k)) * Fr (p k))) -
    (lam * lam') ** serie (fun k => [1-] not_first_repr carAB p k *
      (mu d1' (carAB (p k)) * Fr (p k))) <= ep + ep').
  (* Simplify [d1'] and [d2'] *)
  transitivity (serie 
    (fun k => [1-] not_first_repr carAB p k * (mu d2 (carA (p1 k)) *
      (mu (F2 (p1 k)) (carB (p2 k)) * Fr (p k)))) -
     (lam * lam') ** serie
    (fun k => [1-] not_first_repr carAB p k * (mu d1 (carA (p1 k)) *
      (mu (F1 (p1 k)) (carB (p2 k)) * Fr (p k))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro k; Usimpl.
    simpl; rewrite Umult_assoc; Usimpl.
    rewrite <-(mu_stable_mult_right d2).
    apply (mu_monotonic d2); refine (ford_le_intro _); intro a'.
    apply (cover_elim (carA_prop (p1 k)) a'); [ auto | | ]; intros [H4 H5];
      rewrite H5; Usimpl.
      rewrite <-(mu_zero (F2 a')); apply (mu_monotonic (F2 a')); intro b';
        unfold carAB, carProd, fzero; simpl; unfold p1 in H5; rewrite H5; trivial.
      rewrite H4; apply (mu_monotonic (F2 a')); intro b';
        unfold carAB, carProd; simpl; trivial.
    (* right term *)
    apply multRU_le_compat; [ apply Rmult_le_pos; fourier | apply Rle_refl | ].
    apply serie_le_compat; intro k; Usimpl.
    simpl; rewrite Umult_assoc; Usimpl.
    rewrite <-(mu_stable_mult_right d1).
    apply (mu_monotonic d1); refine (ford_le_intro _); intro a'.
    apply (cover_elim (carA_prop (p1 k)) a'); [ auto | | ]; intros [H4 H5];
      rewrite H5; Usimpl.
      rewrite <-(mu_zero (F1 a')); apply (mu_monotonic (F1 a')); intro b';
        unfold carAB, carProd, fzero; simpl; unfold p1 in H5; rewrite H5; trivial.
      rewrite H4; apply (mu_monotonic (F1 a')); intro b';
        unfold carAB, carProd; simpl; unfold p1 in H5; rewrite H5; auto.
  (* Write the sum over a pair as two nested sums and
     factorize some terms*)
  unfold carAB, p1, p2.
  rewrite (sigma_prod_split_r _ _ p carA_prop carB_prop
    (fun ab => mu d2 (carA (fst ab)) * (mu (F2 (fst ab)) 
      (carB (snd ab)) * Fr ab))),
    (sigma_prod_split_r _ _ p carA_prop carB_prop
      (fun ab => mu d1 (carA (fst ab)) * (mu (F1 (fst ab)) 
        (carB (snd ab)) * Fr ab))); simpl.
  transitivity (serie (fun ka =>
    [1-] not_first_repr carA (fun k => fst (p k)) ka *
    mu d2 (carA (fst (p ka))) *
    serie (fun kb =>
       [1-] not_first_repr carAB p kb *
       carA (fst (p kb)) (fst (p ka)) *
       (mu (F2 (fst (p ka))) (carB (snd (p kb))) *
         Fr (fst (p ka), snd (p kb))))) -
    (lam * lam') ** serie (fun ka =>
      [1-] not_first_repr carA (fun k => fst (p k)) ka *
      serie (fun kb =>
        [1-] not_first_repr carAB p kb *
        carA (fst (p kb)) (fst (p ka)) *
        (mu d1 (carA (fst (p ka))) *
          (mu (F1 (fst (p ka))) (carB (snd (p kb))) *
           Fr (fst (p ka), snd (p kb))))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro k.
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-serie_mult.
    apply serie_le_compat; intro kb; auto.
    apply wretract_le with (fun kb => [1-] not_first_repr carAB p kb *
     carA (p1 kb) (fst (p k)) * mu (F2 (fst (p k))) (carB (p2 kb))); [ auto | ].
    apply (wretract_prod_eq_proj1 _ _ _ _ carA_prop carB_prop).
    (* right term *)
    apply multRU_le_compat; [ apply Rmult_le_pos; fourier | apply Rle_refl | ].
    apply serie_le_compat; intro ka; Usimpl.
    apply serie_le_compat; intro kb; auto.
  (* Push [lam'] inside the serie *)
  rewrite Uminus_le_compat_right with (y:= lam ** serie
     (fun ka =>
      [1-] not_first_repr carA p1 ka *
      mu d1 (carA (p1 ka)) * (lam' **
      serie (fun kb => [1-] not_first_repr carAB p kb * 
        carA (fst (p kb)) (fst (p ka)) *
         (mu (F1 (fst (p ka))) (carB (snd (p kb))) *
            Fr (fst (p ka), snd (p kb))))))).
  Focus 2.
  unfold p1, p2.
  rewrite <-(Rmult_multRU_assoc _ Hlam Hlam').
  apply multRU_le_compat; [ fourier | apply Rle_refl | ].
  rewrite <-(multRU_serie _ Hlam').
  apply serie_le_compat; intro ka.
  rewrite (Umult_sym ([1-] _) (serie _)), <-(Umult_multRU_assoc _ _ Hlam'),
   <-Umult_assoc, (Umult_sym (_ ** _)); Usimpl.
  rewrite Umult_sym, (Umult_multRU_assoc _ _ Hlam').
  apply multRU_le_compat; [ fourier | apply Rle_refl | ].
  rewrite Umult_sym, serie_mult_le.
  apply serie_le_compat; intro kb; auto.
  (* Push both inner series inside the functions measured by
     distributions [F1 (p1 ka)] and  [F2 (p1 ka)] respectively *) 
  transitivity (
    serie  (fun ka => [1-] not_first_repr carA p1 ka *
      mu d2 (carA (p1 ka)) * mu (F2 (p1 ka)) (serie_fun (Mr (p1 ka)))) -
    lam ** serie (fun ka => [1-] not_first_repr carA p1 ka *
      mu d1 (carA (p1 ka)) * (lam' **
        mu (F1 (p1 ka)) (serie_fun (Mr (p1 ka)))))).
  apply Uminus_le_compat.
    (* left term *)
    apply serie_le_compat; intro ka.
    apply Umult_le_compat_right.
    rewrite mu_serie_eq.
    apply serie_le_compat; intro kb.
    unfold Mr.
    rewrite (Umult_sym), <-Umult_assoc, <-mu_stable_mult_right.
    apply mu_monotonic; intro b.
    rewrite <-(Umult_assoc (carB _ _)), <-(Umult_assoc _ (_ * _)); 
      apply Umult_le_compat_right; auto.
    intros b; unfold Mr.
    apply wretract_le with (fun k => [1-] not_first_repr carAB p k * carAB (p k) (p1 ka,b)).
      intros k; rewrite Ule_mult_right, <-Umult_sym;
      unfold carAB at 3, carProd, p1; simpl; auto.
    apply (enum_wretract_eq _ _ carAB_prop).
    (* right term *)
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    apply serie_le_compat; intro ka.
    apply Umult_le_compat_right.
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    rewrite mu_serie_le. 
    apply serie_le_compat; intro kb.
    unfold Mr.
    rewrite (Umult_sym), <-Umult_assoc, <-mu_stable_mult_right.
    apply mu_monotonic; intro b.
    rewrite <-(Umult_assoc (carB _ _)), <-(Umult_assoc _ (_ * _)); 
      apply Umult_le_compat_right; auto.
  (* Transitivity with .... and bound the left-most term by [ep'] *)
  rewrite Uminus_triang_ineq with (c:= serie (fun ka =>
      [1-] not_first_repr carA p1 ka * mu d2 (carA (p1 ka)) *
      (lam' ** mu (F1 (p1 ka)) (serie_fun (Mr (p1 ka)))))).
  rewrite (Uplus_sym ep); apply Uplus_le_compat.
    transitivity (serie (fun ka => ep' * 
      ([1-] not_first_repr carA p1 ka * mu d2 (carA (p1 ka))))).
      rewrite serie_minus_le; unfold fminus.
      apply serie_le_compat; intro ka.
      rewrite <-(mu_stable_mult d2 ([1-] _)), <- 2 (mu_stable_mult_right d2),
       <-(mu_stable_mult d2 ep'), mu_stable_le_minus.
      apply range_le with (1:=HSd2).
        intros a Ha; unfold fmult.
        apply (cover_elim (carA_prop (p1 ka)) a); [auto | | ]; intros [H1 H2];
          rewrite H2; repeat Usimpl; trivial.
          rewrite H1.
          rewrite <-Uminus_distr_right; Usimpl.
          apply (d_expr_le_elim _ _ _ _ _ _ (HF _ Ha (serie_fun (Mr a)))).
    rewrite (serie_mult _ (enum_wretact_mu d2 _ p1 carA_prop)); trivial.
  (* Push term [lam' ** mu (F1 (p1 ka)) (serie_fun (Mr (p1 ka)))] inside 
     the functions measured by distributions [d1] and [d2] *)
  transitivity (mu d2 (serie_fun Mr') - lam ** mu d1 (serie_fun Mr')).
    apply Uminus_le_compat.
    (* left term *)
    rewrite mu_serie_eq. 
    apply serie_le_compat; intro ka; unfold Mr'.
    rewrite <-(mu_stable_mult d2 ([1-] not_first_repr carA p1 ka)),
      <-(mu_stable_mult_right d2).
    apply mu_monotonic; intro a; unfold fmult; auto.
    intro a; unfold Mr'.
    apply wretract_le with (fun k => [1-] not_first_repr carA p1 k *
      carA (p1 k) a); [ auto | ].
    apply (enum_wretract_eq _ _ carA_prop).
    (* right term *) 
    apply multRU_le_compat; [ fourier | apply Rle_refl | ].
    rewrite mu_serie_le.
    apply serie_le_compat; intro ka; unfold Mr'.
    rewrite <-(mu_stable_mult d1 ([1-] not_first_repr carA p1 ka)),
       <-(mu_stable_mult_right d1).
     apply mu_monotonic; intro a; unfold fmult; auto.
  (* Apply hypothesis regarding the distance between [d1] and 
     [d2] to conclude *)
  apply (d_expr_le_elim _ _ _ _ _ _ (Hd (serie_fun Mr'))).
 Qed.

 Lemma le_dist_Mlet_discr: forall S,
   range S d1 ->
   range S d2 ->
   le_dist d1 d2 lam ep -> 
   (forall a, S a -> le_dist (F1 a) (F2 a) lam' ep') -> 
   le_dist (Mlet d1 F1) (Mlet d2 F2) (lam * lam') (ep + ep').
 Proof.
  intros S HSd1 HSd2 Hd HF f.
  setoid_replace (Mlet d1 F1) with (Msnd d1').
    Focus 2.
    unfold d1', Msnd; rewrite Mcomp.
    apply Mlet_eq_compat; trivial.
    apply ford_eq_intro; intro a.
    rewrite (Msnd_prod_distr (Munit a) (F1 a)).
    refine (ford_eq_intro _); intro f'.
    unfold fcte, fone; simpl.
    apply (mu_stable_eq (F1 a)).
    refine (ford_eq_intro _); intro b; auto.
  setoid_replace (Mlet d2 F2) with (Msnd d2').
    Focus 2.
    unfold d2', Msnd; rewrite Mcomp.
    apply Mlet_eq_compat; trivial.
    apply ford_eq_intro; intro a.
    rewrite (Msnd_prod_distr (Munit a) (F2 a)).
    refine (ford_eq_intro _); intro f'.
    unfold fcte, fone; simpl.
    apply (mu_stable_eq (F2 a)).
    refine (ford_eq_intro _); intro b; auto.
  apply (le_dist_Mlet _ (le_dist_Mlet_prod_discr HSd1 HSd2 Hd HF)).
 Qed.

End LE_DIST_MLET_DISCR.

End LE_DIST.


Add Parametric Morphism A: (@le_dist A)
with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr A) ==> 
 (@eq R)  ==> Oeq (O:=U) ==> inverse impl
as le_dist_eq_compat_morph.
Proof.
 unfold le_dist, impl.
 intros d1 d1' Hd1 d2 d2' Hd2  lam ep ep' Hep H f.
 rewrite Hep, <-(H f).
 apply d_expr_eq_compat; auto. 
Qed.


(* [Lambda-Epsilon]-Lift of a relation to distributions *)
Section LE_LIFT.

 Record le_lift A B (S:A -> B -> Prop) (d:Distr (A * B))
  (d1:Distr A) (d2:Distr B) (lam:R) (ep:U) := 
  Build_elift
  {
   le_lam : (1 <= lam)%R;
   le_d   : forall f g,
    max (d_expr (Mfst d) d1 lam f f) (d_expr (Msnd d) d2 lam g g) <= ep;
   le_r   : range (prodP S) d;
   le_p1  : forall f, mu (Mfst d) f <= mu d1 f;
   le_p2  : forall f, mu (Msnd d) f <= mu d2 f
  }.

 Lemma le_lift_elim: forall A B (S:A -> B -> Prop) (d1:Distr A) (d2:Distr B) 
  d (lam:R) ep (f:A -o> U) (g:B -o> U),
  (forall a b, S a b -> f a == g b) ->
  le_lift S d d1 d2 lam ep ->
  d_expr d1 d2 lam f g <= ep.
 Proof.
  intros A B S d1 d2 d lam ep f g Hfg (Hlam, Hdist, Hrange, Hp1, Hp2). 
  apply d_expr_le_intro; trivial.
  rewrite (Uminus_le_compat_right _ (lam ** (mu (Msnd d)) g)). 
  rewrite <-(Hdist f g), <-max_le_left; apply Ule_plus_left.
  apply multRU_le_compat; trivial.      
  fourier.
  rewrite <-Hp1; unfold Mfst, Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hrange); intros; apply (Hfg _ _ H).
  rewrite (Uminus_le_compat_right _ (lam ** (mu (Mfst d)) f)). 
  rewrite <-(Hdist f g), <-max_le_right; apply Ule_plus_left.
  apply multRU_le_compat; trivial.      
  fourier.
  rewrite <-Hp2; unfold Mfst, Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hrange); intros; apply (Hfg _ _ H).
 Qed.

 Lemma le_lift_true : forall A B (d1:Distr A) (d2:Distr B) lam,
  (1 <= lam)%R ->
  le_lift (fun _ _ => True) (prod_distr d1 d2) d1 d2 lam
  ([1-] (lam ** (min (mu d1 (fone _)) (mu d2 (fone _))))).
 Proof.
  intros A B d1 d2 lam.
  constructor; trivial.
  (* distance *)
  intros f g; apply max_le.
  rewrite Mfst_prod_distr. 
  rewrite d_expr_distr_mult; trivial.
  apply Uinv_le_compat, multRU_le_compat; trivial; fourier.

  rewrite Msnd_prod_distr. 
  rewrite d_expr_distr_mult; trivial.
  apply Uinv_le_compat, multRU_le_compat; trivial; fourier.

  (* range *)
  apply range_True.

  (* projections *)
  intros.
  apply (mu_monotonic d1 (fun x : A => (mu d2) (fun _ : B => f x)) f).
  refine (ford_le_intro _); intro a; apply mu_cte_le.
  intros; rewrite (mu_cte_le d1 (mu d2 (fun b => f b))).
  apply mu_monotonic; auto.
 Qed.

 Lemma le_lift_Munit : forall A (x y:A) (P:relation A) (lam:R) , 
  (1 <= lam)%R ->
  P x y -> 
  le_lift P (Munit (x,y)) (Munit x) (Munit y) lam 0.
 Proof.
  intros; constructor; trivial.
  (* distance *)
  intros.
  unfold Mfst, Msnd; repeat rewrite Mlet_unit, d_expr_nul; auto.
  (* range *)
  apply range_Munit with (1:=H0).
 Qed.

 Lemma le_lift_Mlet : forall (A1 A2 B1 B2: Type) (R1: A1 -> B1 -> Prop)
  (R2:A2 -> B2 -> Prop) (ABeqU: (A1 * B1)  -> (A1 * B1) -O-> U) (d:Distr (A1 * B1)) 
  (d1:Distr A1) (d2:Distr B1) (F:A1 * B1 -> Distr (A2 * B2))
  (F1:A1 -> Distr A2) (F2:B1 -> Distr B2) (lam lam':R) (ep ep':U),
  (forall ab : A1 * B1, cover (eq ab) (ABeqU ab)) ->
  is_Discrete d ->
  (1 <= lam')%R -> 
  le_lift R1 d d1 d2 lam ep ->
  (forall (x:A1) (y:B1), R1 x y -> le_lift R2 (F (x, y)) (F1 x) (F2 y) lam' ep') ->
  le_lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) 
  (lam * lam') 
  (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  intros A1 A2 B1 B2 R1 R2 ABeqU d d1 d2 F F1 F2 lam lam' ep ep' HeqU Hdiscr Hlam'
   (Hlam, Hd_dist, Hd_ran, Hp1d, Hp2d) HF.
  constructor.
  transitivity (1 * 1)%R; auto with real.
  (* distance *)
  intros.
  apply (Ueq_orc ep' 1); [apply Ule_class | | ]; intro Hep'.
  (* case [ep'=1] *)
  rewrite  <-(max_le_right (ep + lam ** ep')), <-multRU_ge1, Hep', 
   <-(Uplus_sym 1), <-(Ule_plus_right 1).
  apply Unit.
  trivial.
  (* case [ep' < 1] *) 
  apply (Ule_diff_lt (Unit ep')) in Hep'.
  apply max_le; apply d_expr_le_intro; try (transitivity (1 * 1)%R; auto with real).

  (* 1st *)
  rewrite  <-(max_le_right).
  rewrite (Uminus_triang_ineq _ _ (lam ** (mu (Mlet (Mfst d) F1) f)));
   apply Uplus_le_compat.
  rewrite <-(Hd_dist (fun x : A1 => (mu (F1 x)) f) (fzero _)), 
   <-max_le_right; apply Ule_plus_left.
  rewrite <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; trivial.
  fourier.
  unfold Mfst; repeat rewrite Mlet_simpl; rewrite <-(Rmult_mu _ HeqU Hdiscr Hlam'), mu_stable_le_minus.
  rewrite <-(mu_cte_le d ep'); unfold fcte.
  apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
  rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_right; apply Ule_plus_left.

  (* 2nd *)
  rewrite <-(max_le_left).
  rewrite (Uminus_triang_ineq _ _ (lam' ** (mu (Mlet (Mfst d) F1) f))); 
   apply Uplus_le_compat.
  unfold Mfst; repeat rewrite Mlet_simpl; rewrite <-(Rmult_mu _ HeqU Hdiscr Hlam'), mu_stable_le_minus.
  rewrite <-(mu_cte_le d ep'); unfold fcte.
  apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
  rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_right; apply Ule_plus_right.
  rewrite Rmult_comm, <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; trivial.
  fourier.
  rewrite <-(Hd_dist (fun x : A1 => (mu (F1 x)) f) (fzero _)), 
   <-max_le_right; apply Ule_plus_right.

  (* 3rd *)
  rewrite <-(max_le_right).
  rewrite (Uminus_triang_ineq _ _ (lam ** (mu (Mlet (Msnd d) F2) g)));
   apply Uplus_le_compat.
  rewrite <-(Hd_dist (fzero _) (fun x  => (mu (F2 x)) g)), <-max_le_left.
  apply Ule_plus_left.
  rewrite <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; trivial.
  fourier.
  unfold Msnd; repeat rewrite Mlet_simpl; rewrite <-(Rmult_mu _ HeqU Hdiscr Hlam'), mu_stable_le_minus.
  rewrite <-(mu_cte_le d ep'); unfold fcte.
  apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
  rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_left; apply Ule_plus_left.


  (* 4th *)  
  rewrite  <-(max_le_left).
  rewrite (Uminus_triang_ineq _ _ (lam' ** (mu (Mlet (Msnd d) F2) g))); 
   apply Uplus_le_compat.
  unfold Msnd; repeat rewrite Mlet_simpl; rewrite <-(Rmult_mu _ HeqU Hdiscr Hlam'), mu_stable_le_minus.
  rewrite <-(mu_cte_le d ep'); unfold fcte.
  apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
  rewrite <-(le_d (HF _ _ Hab) f g), <-max_le_left; apply Ule_plus_right.
  trivial.
  rewrite Rmult_comm, <-Rmult_multRU_assoc; trivial.
  rewrite multRU_distr_minus_l; trivial.
  apply multRU_le_compat; trivial.
  fourier.
  rewrite <-(Hd_dist (fzero _) (fun x => (mu (F2 x)) g)), 
   <-max_le_left; apply Ule_plus_right.

  (* range *)
  apply range_Mlet with (prodP R1).
  exact Hd_ran. 
  intros (a,b) H'; apply (le_r (HF _ _ H')).    
  
  (* projections *)
  intros.
  rewrite Mlet_simpl, <-Hp1d; unfold Mfst; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p1 (HF a1 b1 Hab) _).
  intros.
  rewrite Mlet_simpl, <-Hp2d; unfold Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p2 (HF a1 b1 Hab) _).
 Qed.

  Lemma le_lift_discr_witness: forall A B  (carB : B -> MF B) (carA : A -> MF A) 
   (d:Distr (A * B)) (d1:Distr A) (d2:Distr B) R lam ep,
  (forall a, cover (fun x => a = x) (carA a)) ->
  (forall b, cover (fun x => b = x) (carB b)) ->
  is_Discrete d1 ->
  is_Discrete d2 ->
  le_lift R d d1 d2 lam ep ->
  is_Discrete d.
 Proof.
  intros A B carA carB d d1 d2 R lam ep HcarA HcarB Hd1 Hd2 Hd.
  apply (discr_projs _ _ HcarB HcarA).
    apply discr_ext with (2:=Hd1).
    intros; apply Ule_zero_eq; rewrite (le_p1 Hd f); auto.
    apply discr_ext with (2:=Hd2).
    intros; apply Ule_zero_eq; rewrite (le_p2 Hd f); auto.
 Qed.


 Lemma le_lift_lift : forall A B (R:A -> B -> Prop) (d1:Distr A) (d2:Distr B) d,
  le_lift R d d1 d2 R1 0 <-> lift R d d1 d2.
 Proof.
  split.
  intros (Hlam, Hdist, Hran, Hp1, Hp2).
  constructor.
  intro f.
  rewrite <-Uabs_diff_zero.
  rewrite <-(Ule_zero_eq _ (Ole_trans (max_le_right _ _) (Hdist f (fzero _)))).
  unfold Uabs_diff, d_expr; repeat rewrite multRU_1_l; apply Oeq_refl.
  intro f.
  rewrite <-Uabs_diff_zero.
  rewrite <-(Ule_zero_eq _ (Ole_trans (max_le_left _ _) (Hdist (fzero _) f))).
  unfold Uabs_diff, d_expr; repeat rewrite multRU_1_l; apply Oeq_refl.
  trivial.
  
  intros (Hfst, Hsnd, Hran).
  constructor; auto.
  intros f g.
  setoid_replace (Mfst d) with d1 by refine (ford_eq_intro Hfst).
  setoid_replace (Msnd d) with d2 by refine (ford_eq_intro Hsnd).
  rewrite d_expr_nul, d_expr_nul; auto.
 Qed.

 Lemma le_lift_weaken: forall A B d d1 d2 (P P':A -> B -> Prop) 
  (lam lam':R) (ep ep':U), 
  (forall x y, P' x y -> P x y) ->
  (lam' <= lam)%R ->
  ep' <= ep ->
  le_lift P' d d1 d2 lam' ep' -> 
  le_lift P  d d1 d2 lam ep.
 Proof.
  intros A B d d1 d2 P P' lam lam' ep' ep HP Hlam Hep (Hlam', Hdist, Hran).
  constructor; trivial.
  fourier.
  (* distance *)
  intros f g.
  rewrite <-Hep, <-(Hdist f g).
  apply max_le_compat; apply d_expr_lam_weaken; trivial; fourier.   
  
  (* range *)
  apply range_weaken with (2:=Hran). 
  unfold prodP; auto.
 Qed.
  
 Lemma le_lift_eq_compat : forall A B (S:A -> B -> Prop) 
  (d d':Distr (A * B)) (d1 d1':Distr A) (d2 d2':Distr B) (lam lam':R) (ep ep':U),
  d == d' -> 
  d1 == d1' -> 
  d2 == d2' -> 
  lam = lam' ->
  ep == ep' ->
  le_lift S d d1 d2 lam ep -> le_lift S d' d1' d2' lam' ep'.
 Proof.
  intros A B R d d' d1 d1' d2 d2' 
   lam lam' ep ep' Heq Heq1 Heq2 Heq3 Heq4 (Hlam, Hdist, Hran, Hp1, Hp2).
  constructor.
  fourier.
  intros; unfold Mfst, Msnd.
  rewrite <-(@Mlet_eq_compat _ _  d d' (fun ab => Munit (fst ab)) 
   (fun ab => Munit (fst ab)) Heq (Oeq_refl _)).
  rewrite <-(@Mlet_eq_compat _ _  d d' (fun ab => Munit (snd ab)) 
   (fun ab => Munit (snd ab)) Heq (Oeq_refl _)).
  rewrite <-Heq1, <-Heq2, <-Heq3, <-Heq4.
  apply Hdist.
  apply range_stable_eq with (1:=Heq); trivial.
  intro f; rewrite <-(eq_distr_elim Heq1), <-Hp1.
  apply eq_distr_elim; rewrite Heq; trivial.
  intro f; rewrite <-(eq_distr_elim Heq2), <-Hp2.
  apply eq_distr_elim; rewrite Heq; trivial.
 Qed.

 Lemma le_lift_transp : forall A B (d:Distr (A * B)) (d1:Distr A) (d2:Distr B) 
  R lam ep, 
  le_lift (fun b a => R a b) 
  (Mlet d (fun ab => Munit (snd ab, fst ab))) d2 d1 lam ep ->
  le_lift R d d1 d2 lam ep. 
 Proof.
  intros A B d d1 d2 R lam ep (Hlam, Hdist, Hran, Hp1, Hp2).
  constructor; trivial.
  (* distance *)
  intros f g;  apply max_le.
  rewrite <-(Hdist g f), <-max_le_left; auto.
  rewrite <-(Hdist g f), <-max_le_right; auto.
  
  (* range *)
  intros f Hf.
  rewrite (Hran (fun ba => f (snd ba,fst ba))).
  rewrite Mlet_simpl; simpl.
  apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a,b); trivial.
  auto.
 Qed.

 Lemma le_lift_prod : forall A B (d:Distr (A * B)) (P:A -> B -> Prop),
  range (prodP P) d ->
  le_lift P d (Mfst d) (Msnd d) R1 0.
 Proof. 
  intros; constructor; trivial.
  intros; repeat rewrite d_expr_nul; auto with real.
 Qed.

 Lemma le_lift_distr0: forall (A B:Type) P lam ep,
   (1 <= lam)%R ->
   le_lift P (distr0 (A*B)) (distr0 A) (distr0 B) lam ep. 
 Proof.
  intros.
  constructor.
    trivial.
    intros; unfold Mfst, Msnd.
    rewrite 2 Mlet_distr0_abs, 2 (d_expr_nul _ _ H).
    unfold max; repeat Usimpl; auto.
    intros f _; trivial.
    intros; unfold Mfst; rewrite Mlet_simpl; trivial.
    intros; unfold Msnd; rewrite Mlet_simpl; trivial.
 Qed.


 (* Sufficient condition to relate two distibutions wrt 
    the equalitiy relation *)
 Section LE_DIST_2_LE_LIFT.

  Variable A : Type.

  Variable AeqU : A -> A -O-> U.
  Hypothesis cover_uR : forall a : A, cover (eq a) (AeqU a).

  Variable d1 d2 : Distr A.
  Hypothesis H_d1 : is_Discrete d1.
  Hypothesis H_d2 : is_Discrete d2.

  Let p := parity_split (D_points H_d1) (D_points H_d2).
  Let dd := Mlet (dmin _ cover_uR p d1 d2) (fun a => Munit (a,a)).
 
  Lemma le_lift_eq_intro: forall lam ep,
   (1 <= lam)%R ->
   le_dist d1 d2 lam ep ->
   le_lift (@eq A) dd d1 d2 lam ep.
  Proof.
   intros.
   constructor; trivial.

   (* distance *)
   set (P:=fun a : A => Uleb (mu d1 (AeqU a)) (mu d2 (AeqU a))).
   intros f g; apply max_le.
   apply d_expr_le_intro; trivial.
   (*   *)
   change (mu d1 f - lam ** (mu (dmin AeqU cover_uR p d1 d2) f) <= ep).
   rewrite (mu_restr_split d1 P).
   eapply Ole_trans with (_ - lam ** _).
   apply Uminus_le_compat_right.
   apply multRU_le_compat.
   fourier.
   trivial.
   apply Oeq_le; symmetry.
   apply (dmin_simpl _ cover_uR (disc_eqpoint_l H_d1 H_d2)
     (disc_eqpoint_r H_d1 H_d2) _ Uleb_correct_conv  Uleb_complete_conv f).

   rewrite <-multRU_distr_plus_l, Uplus_minus_perm_assoc; trivial.
   match goal with |- ?X1 + _ <= _ => setoid_replace X1 with (@D0 U) by auto end.
   Usimpl.
   pose proof (H0 (restr (negP P) f)) as Haux.
   apply d_expr_le_elim in Haux.
   apply (proj2 Haux).
   change (mu (dmin AeqU cover_uR p d1 d2) f - lam ** (mu d1) f <= ep).
   rewrite <-multRU_ge1, Uminus_le_zero; trivial.
   apply (@dmin_le_d1 _ _ cover_uR p d1 d2 (disc_eqpoint_l H_d1 H_d2)).

   (*   *)
   apply d_expr_le_intro; trivial.
   change (mu d2 g - lam ** (mu (dmin AeqU cover_uR p d1 d2) g) <= ep).
   unfold p.
   rewrite (mu_restr_split d2 P).
   rewrite
    (dmin_simpl _ cover_uR (disc_eqpoint_l H_d1 H_d2)   
     (disc_eqpoint_r H_d1 H_d2) _ Uleb_correct_conv  Uleb_complete_conv g).
   rewrite <-multRU_distr_plus_l, Uplus_minus_perm_assoc; trivial.
   match goal with |- _ + ?X1 <= _ => setoid_replace X1 with (@D0 U) by auto end.
   Usimpl.
   pose proof (H0 (restr P g)) as Haux.
   apply d_expr_le_elim in Haux.
   apply (proj1 Haux).   
   change (mu (dmin AeqU cover_uR p d1 d2) g - lam ** (mu d2) g <= ep).
   rewrite <-multRU_ge1, Uminus_le_zero; trivial.
   apply (@dmin_le_d2 _ _ cover_uR p d1 d2 (disc_eqpoint_r H_d1 H_d2)).

   (* range *)
   eapply range_Mlet with (1:=range_True _).
   intros a _; apply (range_Munit _ _ _ (eq_refl a)).

   (* projections *)
   intro; unfold dd, Mfst.
   rewrite 2 Mlet_simpl.
   apply (@dmin_le_d1 _ _ cover_uR p d1 d2 (disc_eqpoint_l H_d1 H_d2) f).
   intro; unfold dd, Msnd.
   rewrite 2 Mlet_simpl.
   apply (@dmin_le_d2 _ _ cover_uR p d1 d2 (disc_eqpoint_r H_d1 H_d2) f).
  Qed.

 End LE_DIST_2_LE_LIFT.




(* Transitivity of the lift *)
Section LIFT_TRANS.
 
 Variables A B C : Type.
 Variable carA : A -> MF A.
 Variable carB : B -> MF B.
 Variable carC : C -> MF C.

 Hypothesis carA_prop : forall b, cover (fun x => b = x) (carA b).
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 Hypothesis carC_prop : forall b, cover (fun x => b = x) (carC b).

 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable S : A -> C -> Prop.

 Hypothesis P_Q_S : forall x y z, P x y -> Q y z -> S x z.

 Variable d  : Distr (A*B).
 Variable d' : Distr (B*C). 
 Variable ep ep' : U.
 Variable lam lam': R.

 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Hypothesis  Hd : le_lift  P d  d1 d2 lam ep.
 Hypothesis  Hd': le_lift Q d' d2 d3 lam' ep'.

 Hypothesis Hd1_discr: is_Discrete d1.
 Hypothesis Hd2_discr: is_Discrete d2.
 Hypothesis Hd3_discr: is_Discrete d3.


 Lemma Hd_discr: 
   is_Discrete d.
 Proof.
  apply (discr_projs _ _ carB_prop carA_prop).
    refine (discr_ext _ _ Hd1_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p1 Hd), H; trivial.
    refine (discr_ext _ _ Hd2_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p2 Hd), H; trivial.
 Qed.

 Lemma Hd'_discr: is_Discrete d'.
 Proof.
  apply (discr_projs _ _ carC_prop carB_prop).
    refine (discr_ext _ _ Hd2_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p1 Hd'), H; trivial.
    refine (discr_ext _ _ Hd3_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p2 Hd'), H; trivial.
 Qed.


 Let carAB: A*B -> MF (A*B) := carProd carA carB.
 Let carBC: B*C -> MF (B*C) := carProd carB carC.
 Let carAB_prop: forall ab, cover (fun x => ab = x) (carAB ab).
 Proof.
  apply (carProd_prop _ _ carA_prop carB_prop).
 Qed.
 Let carBC_prop: forall bc, cover (fun x => bc = x) (carBC bc). 
 Proof.
  apply (carProd_prop _ _ carB_prop carC_prop).
 Qed.

 Definition dfst (b : B) : Distr (B*C) := distr_mult (fun q => carB b (fst q)) d'.
 Definition dsnd (b : B) : Distr (A*B) := distr_mult (fun q => carB b (snd q)) d.

 Let dsnd_le : forall b, 
  mu (dsnd b) (fone _) <= mu d2 (fun b' => carB b b').
 Proof.
  intro; rewrite <-(le_p2 Hd); simpl;
    apply (mu_monotonic d); intro; auto.
 Qed. 

 Let dfst_le : forall b, 
  mu (dfst b) (fone _) <=  mu d2 (fun b' => carB b b').
 Proof.
  intro; rewrite <-(le_p1 Hd'); simpl;
    apply (mu_monotonic d'); intro; auto.
  Qed.

 Let d_restr : B -> Distr (A*B) := 
  fun b => distr_div (mu d2 (fun b' => carB b b')) (dsnd b) (dsnd_le b) .

 Let d'_restr : B -> Distr (B*C) := 
  fun b => distr_div  (mu d2 (fun b' => carB b b')) (dfst b) (dfst_le b).


 Definition dd' : Distr (A * C) := 
  Mlet d2 (fun b => 
   Mlet (d_restr b) (fun p => 
    Mlet (d'_restr b) (fun q => Munit (fst p, snd q)))).


 Lemma dd'_comm: dd' ==
   Mlet d2 (fun b => 
     Mlet (d'_restr b) (fun q => 
       Mlet (d_restr b) (fun p => Munit (fst p, snd q)))).
 Proof.
  apply eq_distr_intro; intro f.
  unfold dd'; rewrite 2 Mlet_simpl; simpl.
  apply (mu_stable_eq d2); refine (ford_eq_intro _); intro b.
  apply Udiv_eq_compat; [ | auto ].
  transitivity (mu d (fdiv (mu d2 (fun b' => carB b b')) 
    (fun ab => mu d' (fun bc => carB b (snd ab) * 
      (carB b (fst bc) * f (fst ab, snd bc)))))). 
    unfold fdiv; apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab.
    rewrite <-Umult_div_assoc, <-(mu_stable_mult d' 
      (carB b (snd ab))); trivial.
    rewrite <-(le_p1 Hd'); simpl; apply (mu_monotonic d'); 
      intro bc; auto.
  transitivity (mu d' (fdiv (mu d2 (fun b' => carB b b')) 
    (fun bc => mu d (fun ab =>  carB b (fst bc) * 
      (carB b (snd ab) * f (fst ab, snd bc)))))).
    Focus 2.
    unfold fdiv; apply (mu_stable_eq d'); refine (ford_eq_intro _); intro bc.
    rewrite <-Umult_div_assoc, <-(mu_stable_mult d 
      (carB b (fst bc))); trivial.
    rewrite <-(le_p2 Hd); simpl; apply (mu_monotonic d); 
      intro ab; auto.
    unfold fdiv; rewrite 2 mu_stable_div_strong.
      apply Udiv_eq_compat_left.
      rewrite (@Discr_distr_comm_elim _ _ _ d d' carAB_prop Hd_discr).
      apply mu_stable_eq; refine (ford_eq_intro _); intro bc.
      apply mu_stable_eq; refine (ford_eq_intro _); trivial.
      unfold fcte; intros bc. 
      rewrite <-(le_p2 Hd); simpl.
      apply (mu_monotonic d); intro ab; rewrite Umult_sym, <-Umult_assoc; auto.
      unfold fcte; intros ab.
      rewrite <-(le_p1 Hd'); simpl.
      apply (mu_monotonic d'); intro bc; rewrite Umult_sym, <-Umult_assoc; auto. 
 Qed.


 Lemma Mfst_dd'_le_Mfst_d: Mfst dd' <= Mfst d.
 Proof.
  refine (ford_le_intro _); intro f.
  unfold Mfst, dd'; repeat rewrite Mlet_simpl; simpl.
  rewrite <-(distr_pointwise_sum_r _ carB_prop Hd2_discr d (le_p2 Hd)).
  apply (mu_monotonic d2); intro b.
  apply Udiv_le_compat; [ | apply (mu_stable_eq d2);
    refine (ford_eq_intro _); trivial ].
  apply (mu_monotonic d); intro ab.
  rewrite (mu_stable_mult_right d' (f (fst ab))). 
  rewrite (Umult_sym _ (f _)), (Umult_div_assoc _ _ _ 
    (le_p1 Hd' (fun b' : B => carB b b'))), Umult_assoc; auto.
 Qed.


 Lemma Msnd_dd'_le_Msnd_d': Msnd dd' <= Msnd d'.
 Proof.
  refine (ford_le_intro _); intro f.
  unfold Msnd; rewrite 2 Mlet_simpl.  
  rewrite <-(distr_pointwise_sum_l _ carB_prop Hd2_discr d' (le_p1 Hd')). 
  rewrite (eq_distr_elim dd'_comm); simpl.
  apply (mu_monotonic d2); intro b.
  apply Udiv_le_compat; [ | apply (mu_stable_eq d2);
    refine (ford_eq_intro _); trivial ].
  apply (mu_monotonic d'); intro bc.
  rewrite (mu_stable_mult_right d (f (snd bc))). 
  rewrite (Umult_sym _ (f _)), (Umult_div_assoc _ _ _ 
    (le_p2 Hd (fun b' : B => carB b b'))), Umult_assoc; auto.
 Qed.


 Lemma dd'_range : range (prodP S) dd'.
 Proof.
  intros h Hf; unfold dd'; simpl.
  rewrite <-(mu_zero d2).
  apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro x; unfold fzero.
  apply (Ueq_orc 0  (mu d2 (fun b' => carB x b'))); [ auto | | ]; intros.
    (*   *)
    apply Oeq_sym; apply Udiv_by_zero; auto.
    (*   *)
    apply Oeq_sym; apply Udiv_zero_eq; auto.
    apply (le_r Hd); intros.
    apply (cover_elim (carB_prop x) (snd x0)); auto; intros [H4 H5]; rewrite H5; Usimpl.
      (*  *)
      trivial.
      (*  *)
      symmetry; apply Udiv_zero_eq.
      apply (le_r Hd'); intros.
      destruct x1; destruct x0; simpl.
      simpl in H4; subst x.
      apply (cover_elim (carB_prop b0) b); auto; intros [H6 H7].
        rewrite H7; auto.
        rewrite H7; Usimpl; subst b0.
        apply Hf; apply P_Q_S with b; trivial.
  Qed.


 Lemma dist_l_aux: le_dist (Mfst dd') (Mfst d) lam' ep'.
 Proof.
  pose proof (le_lam Hd') as Hlam'.
  assert (Hr: is_Discrete (Mfst d)) by 
    apply (is_Discrete_Mlet _ Hd_discr (fun ab => (is_Discrete_Munit (fst ab)))).
  destruct Hd_discr as (p,Hp); simpl.
  set (p2:=fun k' : nat => snd (p k')).
  (* Use lemma [le_dist_discr_ub_le] to bound the distance *)
  eapply le_dist_weaken with (lam':= lam'); [ | split; fourier | 
    apply (@le_dist_discr_ub_le _ _ carA_prop _ _ _  Hlam' _ (D_Discr Hr) Mfst_dd'_le_Mfst_d) ].
  set (P':= restr (fun a => Uleb (lam' ** mu (Mfst dd') (carA a)) 
    (mu (Mfst d) (carA a))) (fone A)).
  (* Simplify distribution [Mfst dd'] *)
  rewrite Uminus_le_compat_right with (y:= lam' ** 
     mu d (fun ab => mu d' (fun bc => carB (snd ab) (fst bc) * P' (fst ab)) /
        mu d2 (fun b' : B => carB (snd ab) b'))).
    Focus 2.  
    apply multRU_le_compat; [ fourier | apply Rle_refl | simpl ].
    rewrite <-(distr_pointwise_sum_r _ carB_prop Hd2_discr d (le_p2 Hd)).
    simpl; apply (mu_monotonic d2); intro b.
    apply Udiv_le_compat.
      apply (mu_monotonic d); intros (a',b'); simpl.
      apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5]; 
        rewrite H5; repeat Usimpl; [ | rewrite H4 ]; trivial.
      apply (mu_stable_eq d2); refine (ford_eq_intro _); intro; trivial.
  (* Discretize the distributions *)
  simpl; rewrite 2 (mu_is_Discrete _ carAB_prop (mkDiscr Hp)); simpl.
  rewrite (discr_distr_simpl _ carAB_prop Hp (fun ab => P' (fst ab))),
   (discr_distr_simpl _ carAB_prop Hp (fun ab => mu d' 
     (fun bc : B * C => carB (snd ab) (fst bc) * P' (fst ab)) /
      mu d2 (fun b'=> carB (snd ab) b'))).
  rewrite <-(multRU_serie _ Hlam'), serie_minus_le; unfold fminus.
  (* Extract as a common factor the term [ [1-] not_first_repr carAB p k * 
     (mu d (carAB (p k)) / mu d2 (fun b' => carB (snd (p k)) b')) ]
     and bound factor [P' (fst (p k))] by [1] *)
  transitivity  (serie (fun k => 
    [1-] not_first_repr carAB p k * mu d (carAB (p k)) * P' (fst (p k)) -
    lam' ** ([1-] not_first_repr carAB p k * 
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b')) *
      mu d' (fun bc => carB (p2 k) (fst bc))))).
    apply serie_le_compat; intro k.
    rewrite Umult_assoc; apply Uminus_le_compat_right.
    apply multRU_le_compat; [ fourier | apply Rle_refl | ]. 
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-Umult_div_assoc, (Umult_sym (mu d _) (mu d' _)),
     (mu_stable_mult_right d'), <-Umult_assoc, (Umult_div_assoc _ (_ * _));
       [ | rewrite <-(le_p2 Hd (fun b' : B => carB (snd (p k)) b')),
       Ule_mult_left; unfold carAB, carProd; simpl; auto | rewrite <-(le_p1 Hd' 
         (fun b' : B => carB (snd (p k)) b')); simpl; auto ].
    unfold p2; rewrite Umult_sym; Usimpl; auto.
  transitivity (serie (fun k =>
    [1-] not_first_repr carAB p k * mu d2 (fun b' => carB (p2 k) b') *
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b')) -
    lam' ** ([1-] not_first_repr carAB p k * mu (Mfst d') (fun b => carB (p2 k) b) *
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b'))))).  
    apply serie_le_compat; intro k.
    apply Uminus_le_compat.
      rewrite <- 2 Umult_assoc; Usimpl.
      apply (Ueq_orc 0 (mu d2 (fun b' => carB (p2 k) b'))); [ auto | | ]; intro H.
        transitivity (@D0 U); [rewrite H | trivial ].
        rewrite <-(le_p2 Hd (fun b' : B => carB (p2 k) b')),
          Ule_mult_right; unfold carAB, carProd; simpl; auto.
        rewrite <-(Umult_sym (_ / _)), (Udiv_mult _ H); trivial.
     rewrite <-(le_p2 Hd (fun b' : B => carB (p2 k) b')),
       Ule_mult_right; unfold carAB, carProd; simpl; auto.
     rewrite <- 2 Umult_assoc, (Umult_sym (mu (Mfst _) _)); trivial.
  set (F := fun b => mu d2 (fun b' => carB b b') -
        lam' ** (mu (Mfst d')) (fun b' => carB b b')).
  set (H:= fun ab => mu d (carAB ab) / mu d2 (fun b' => carB (snd ab) b') * 
    F (snd ab)).
  transitivity (serie (fun k => ([1-] not_first_repr carAB p k * H (p k)))).
    apply serie_le_compat; intro k; unfold H, F.
    apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
      [auto | | ]; intros [_ H5].
    rewrite H5; repeat Usimpl.
    rewrite <-(Umult_multRU_assoc _ _ Hlam'), <-Uminus_distr_left,
     <-(Umult_sym (_ - _)); unfold p2; Usimpl; auto.
    rewrite H5 at 1; repeat Usimpl; trivial.
  (* rewrite the serie as two nested series, one summing over the 
     [a]'s and the other summing over the [b]'s *)
  unfold carAB; rewrite (sigma_prod_split_l _ _ p carA_prop carB_prop).
  (* Push factor [F (p2 kb)] outside the inner serie *)
  transitivity (serie (fun kb => [1-] not_first_repr carB p2 kb *
     F (p2 kb) * serie (fun ka => [1-] not_first_repr carAB p ka *
         carB (p2 ka) (p2 kb) * 
         (mu d (carAB (fst (p ka), p2 kb)) / mu d2 (fun b' => carB (p2 kb) b'))))).
    apply serie_le_compat; intro kb; unfold H.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop 
      (fun k => snd (p k))) kb); [auto | intros _ | intros [_ H5]  ].
      2:rewrite H5; repeat Usimpl; trivial.
      rewrite <-Umult_assoc, <-serie_mult with (c:=F (p2 kb)).
      unfold p2; Usimpl; apply serie_le_compat; intro ka.
      rewrite Umult_assoc, Umult_sym; trivial.
    apply (Ule_orc 1 (mu d2 (fun b' => carB (p2 kb) b'))); 
      [ apply class_wretract | | ]; intro Heq.
    (* case [d2 (p2 kb) == 1] *)
    apply wretract_le with (fun k => [1-] not_first_repr carAB p k * mu d (carAB (p k))).
      intro k; rewrite (Uge_one_eq _ Heq), Udiv_one_strong.
      apply (cover_elim (carB_prop (p2 k)) (p2 kb)); [ auto | | ]; intros (H',H'').
        rewrite H''; repeat Usimpl; trivial.
        rewrite <-H', <-surjective_pairing; auto.
    apply wretract_le with (coeff carAB p d).
      intro k; apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
        [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl.
        rewrite (coeff_first_repr _ carAB_prop Hp _ H5); trivial.
        trivial.
    apply (wretract_coeff _ carAB_prop p d).
    (* case [d2 (p2 kb) < 1] *)
    apply wretract_le with (fun ka  => ([1-] not_first_repr carAB p ka * 
      carB (p2 ka) (p2 kb) * mu d (carAB (fst (p ka), p2 kb))) /
       mu d2 (fun b' => carB (p2 kb) b')).
      intros k.
      apply Oeq_le; symmetry; apply Umult_div_assoc.
      rewrite <-(le_p2 Hd (fun b' => carB (p2 kb) b'));
        simpl; unfold carAB, carProd; auto.
    apply (wretract_Udiv _ Heq).
    intro n.
    rewrite le_lub.
    transitivity (serie (fun k => [1-] not_first_repr carAB p k *
      ((mu d) (carAB (p k)) * carB (p2 kb) (p2 k)))).
      apply lub_le_compat; refine (ford_le_intro _); intro; apply sigma_le_compat; intros.
      apply (cover_elim (carB_prop (p2 k)) (p2 kb)); [ auto | | ]; intros (H',H'').
        rewrite H''; repeat Usimpl; trivial.
        rewrite <-H', <-surjective_pairing, <-Umult_assoc; auto.
    rewrite <-(le_p2 Hd (fun b' => carB (p2 kb) b')); simpl.
    rewrite (mu_is_Discrete _ carAB_prop (mkDiscr Hp)); simpl.
    rewrite (discr_distr_simpl _ carAB_prop Hp) with (f:=fun ab =>
      carB (p2 kb) (snd ab)); trivial.
  (* Bound the inner serie by [1] *)
  rewrite serie_prod_maj.
  (* Split the serie in two *)
  set (PR:= fun b => B2U (Uleb (lam' ** mu (Mfst d') (fun b' => carB b b')) 
    (mu d2 (fun b' => carB b b')))).
  transitivity (serie (fun k => 
       [1-] not_first_repr carB p2 k * PR (p2 k) * 
       mu d2 (fun b' => carB (p2 k) b') -
       lam' ** ([1-] not_first_repr carB p2 k * PR (p2 k) * 
         mu (Mfst d') (fun b' => carB (p2 k) b')))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl; trivial.
      unfold PR, B2U, F.
      match goal with |- context [Uleb ?X1 ?X2] => 
        generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; repeat Usimpl;
          [ trivial | apply (Uminus_le_zero _ _ (Ult_le  Heq)) ]
      end.
  rewrite <-serie_minus_eq.
    Focus 2.
    intros k. 
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat (Usimpl || multRU_simpl); trivial.
    unfold PR, B2U, F.
    match goal with |- context [Uleb ?X1 ?X2] => 
      generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; 
        repeat (Usimpl || multRU_simpl); trivial
    end.
    Focus 2.
    apply wretract_le with (fun k => [1-] not_first_repr carB p2 k *
      mu d2 (fun b' => carB (p2 k) b')); [ auto | ].
    intro n.
    rewrite <-(mu_stable_mult d2 ([1-] _)).
    transitivity ([1-] (sigma (fun k => mu d2
      (fmult ( [1-] not_first_repr carB p2 k) (fun b' => carB (p2 k) b'))) n));
      [ | Usimpl; apply sigma_le_compat; intros k _; apply (mu_stable_mult d2) ].
    rewrite <-mu_sigma_eq.
      (* 1st subg *)
      apply mu_fplusok.
      unfold fplusok, fmult, finv, sigma_fun; intro b; fold (p2 n).
      apply (cover_elim (carB_prop (p2 n)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) n); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'; fold (p2 k').
        apply (cover_elim (carB_prop (p2 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
      (* 2nd subg *) 
      intros b k Hk; unfold fmult; fold (p2 k).
      apply (cover_elim (carB_prop (p2 k)) b); [ auto | | ]; intros [H4 H5].
        rewrite H5; Usimpl; trivial.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
            [auto | | ]; intros [H4' H5']; rewrite H5'; repeat Usimpl; trivial.
        rewrite sigma_zero; [ Usimpl; trivial | ].
        intros k' Hk'; fold (p2 k').
        apply (cover_elim (carB_prop (p2 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  (* Push the factors multiplying the distributions inside the measured functions and
     the [lam'] term outside the rightmost serie *)
  transitivity (serie (fun k => mu d2 (fmult ([1-] not_first_repr carB p2 k * PR (p2 k))
    (fun b => carB (p2 k) b))) -
            lam' ** serie (fun k => mu (Mfst d') (fmult ([1-] not_first_repr carB p2 k * PR (p2 k))
    (fun b => carB (p2 k) b)))).
    apply Uminus_le_compat; [ | rewrite (multRU_serie _ Hlam'); 
      apply multRU_le_compat; [ fourier | apply Rle_refl | ] ];
        apply serie_le_compat; intro k; apply  mu_stable_mult.
  (* Push the series inside the function being measured by [d2] and [Mfst d'] *)
  assert (Haux: forall b, wretract (fun k => fmult ([1-] not_first_repr carB p2 k * PR (p2 k)) 
    (fun b' => carB (p2 k) b') b)).
      intro b. 
      apply wretract_le with  (fun k => carB (p2 k) b * [1-] not_first_repr carB p2 k);
        [ unfold fmult; intro k; rewrite Umult_sym, Umult_assoc; trivial | ].
      intro k.
      apply (cover_elim (carB_prop (p2 k)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'.
        apply (cover_elim (carB_prop (p2 k')) b); auto; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  rewrite <-2 (mu_serie_eq _ _ Haux).
  (* Use the hypothesis about the distance between [d2] and [Mfst d'] 
     to conclude *)
  match goal with |- fmonot _ ?PP' - _ <= _  => set (FF:=PP') end.
  rewrite <-(le_d Hd' FF (fzero _)), <-max_le_right; apply Ule_plus_left.
 Qed.


 Lemma dist_r_aux: le_dist (Msnd dd') (Msnd d') lam ep.
 Proof.
  pose proof (le_lam Hd) as Hlam.
  assert (Hr: is_Discrete (Msnd d')) by 
    apply (is_Discrete_Mlet _ Hd'_discr (fun bc => (is_Discrete_Munit (snd bc)))).
  destruct Hd'_discr as (p,Hp); simpl.
  set (p1:=fun k => fst (p k)).
  (* Use lemma [le_dist_discr_ub_le] to bound the distance *)
  eapply le_dist_weaken with (lam':= lam); [ | split; fourier | 
    apply (@le_dist_discr_ub_le _ _ carC_prop _ _ _  Hlam _ (D_Discr Hr) Msnd_dd'_le_Msnd_d') ].
  set (P':= restr (fun c => Uleb (lam ** mu (Msnd dd') (carC c)) 
    (mu (Msnd d') (carC c))) (fone C)).
  (* Simplify distribution [Msnd dd'] *)
  rewrite Uminus_le_compat_right with (y:= lam ** 
     mu d' (fun bc => mu d (fun ab => carB (fst bc) (snd ab) * P' (snd bc)) /
        mu d2 (fun b' => carB (fst bc) b'))).
    Focus 2.  
    apply multRU_le_compat; [ fourier | apply Rle_refl |  ].
    rewrite <-(distr_pointwise_sum_l _ carB_prop Hd2_discr d' (le_p1 Hd')).
    rewrite (ford_eq_elim (Msnd_eq_compat_morph dd'_comm)).
    simpl; apply (mu_monotonic d2); intro b.
    apply Udiv_le_compat.
      apply (mu_monotonic d'); intros (b',c'); simpl.
      apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5]; 
        rewrite H5; repeat Usimpl; [ | rewrite H4 ]; trivial.
      apply (mu_stable_eq d2); refine (ford_eq_intro _); intro; trivial.
  (* Discretize the distributions *)
  simpl; rewrite 2 (mu_is_Discrete _ carBC_prop (mkDiscr Hp)); simpl.
  rewrite (discr_distr_simpl _ carBC_prop Hp (fun bc => P' (snd bc))), 
   (discr_distr_simpl _ carBC_prop Hp (fun bc => mu d (fun ab => 
     carB (fst bc) (snd ab) * P' (snd bc)) /  mu d2 (fun b'=> carB (fst bc) b'))).
  rewrite <-(multRU_serie _ Hlam), serie_minus_le; unfold fminus.

  (* Extract as a common factor the term ... *)
  transitivity  (serie (fun k => 
    [1-] not_first_repr carBC p k * mu d' (carBC (p k)) * P' (snd (p k)) -
    lam ** ([1-] not_first_repr carBC p k * 
    ((mu d' (carBC (p k)) * P' (snd (p k))) / mu d2 (fun b' => carB (p1 k) b')) *
      mu d (fun ab => carB (p1 k) (snd ab))))).
    apply serie_le_compat; intro k.
    rewrite Umult_assoc; apply Uminus_le_compat_right.
    apply multRU_le_compat; [ fourier | apply Rle_refl | ]. 
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-Umult_div_assoc, (Umult_sym (mu d' _) (mu d _)),
     (mu_stable_mult_right d), <-Umult_assoc, (Umult_div_assoc _ (_ * _));
       [ | rewrite <-(le_p1 Hd' (fun b' => carB (fst (p k)) b')),
       Ule_mult_left; unfold carBC, carProd; simpl; auto | rewrite <-(le_p2 Hd 
         (fun b' => carB (fst (p k)) b')); simpl; auto ].
    unfold p1; rewrite Umult_sym; Usimpl; auto.
  transitivity (serie (fun k =>
    [1-] not_first_repr carBC p k * mu d2 (fun b' => carB (p1 k) b') *
    ((mu d' (carBC (p k)) * P' (snd (p k))) / mu d2 (fun b' => carB (p1 k) b')) -
    lam ** ([1-] not_first_repr carBC p k * mu (Msnd d) (fun b => carB (p1 k) b) *
    ((mu d' (carBC (p k)) * P' (snd (p k))) / mu d2 (fun b' => carB (p1 k) b'))))).  
    apply serie_le_compat; intro k.
    apply Uminus_le_compat.
      rewrite <- 2 Umult_assoc; Usimpl.
      apply (Ueq_orc 0 (mu d2 (fun b' => carB (p1 k) b'))); [ auto | | ]; intro H.
        transitivity (@D0 U); [rewrite H | trivial ].
        rewrite <-(le_p1 Hd' (fun b' : B => carB (p1 k) b')),
          Ule_mult_right; unfold carBC, carProd; simpl; auto.
        rewrite <-(Umult_sym (_ / _)), (Udiv_mult _ H); trivial.
     rewrite <-(le_p1 Hd' (fun b' => carB (p1 k) b')),
       Ule_mult_right; unfold carBC, carProd; simpl; auto.
     rewrite <- 2 Umult_assoc, (Umult_sym (mu (Msnd _) _)); trivial.
  set (F := fun b => mu d2 (fun b' => carB b b') -
        lam ** (mu (Msnd d)) (fun b' => carB b b')).
  set (H:= fun bc => mu d' (carBC bc) / mu d2 (fun b' => carB (fst bc) b') * 
    F (fst bc)).
  transitivity (serie (fun k => ([1-] not_first_repr carBC p k * H (p k)))).
    apply serie_le_compat; intro k; unfold H, F.
    apply (cover_elim (cover_not_first_repr _ _ carBC_prop p) k); 
      [auto | | ]; intros [_ H5].
    rewrite H5; repeat Usimpl.
    rewrite <-(Umult_multRU_assoc _ _ Hlam), <-Uminus_distr_left,
     <-(Umult_sym (_ - _)); unfold p1; Usimpl; auto.
    rewrite H5 at 1; repeat Usimpl; trivial.
  (* rewrite the serie as two nested series, one summing over the 
     [a]'s and the other summing over the [b]'s *)
  unfold carBC; rewrite (sigma_prod_split_r _ _ _ carB_prop carC_prop); fold p1 carBC.
  (* Push factor [F (p1 kb)] outside the inner serie *)
  transitivity (serie (fun kb => [1-] not_first_repr carB p1 kb *
     F (p1 kb) * serie (fun kc => [1-] not_first_repr carBC p kc *
         carB (p1 kb) (p1 kc) * 
         (mu d' (carBC (p1 kb, snd (p kc))) / mu d2 (fun b' => carB (p1 kb) b'))))).
    apply serie_le_compat; intro kb; unfold H.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop 
      p1) kb); [auto | intros _ | intros [_ H5]  ].
      2:rewrite H5; repeat Usimpl; trivial.
      rewrite <-Umult_assoc, <-serie_mult with (c:=F (p1 kb)).
      Usimpl; apply serie_le_compat; intro kc.
      rewrite Umult_assoc, Umult_sym; trivial.
    simpl; unfold p1; repeat Usimpl; apply BaseDef.carA_sym; trivial.
    apply (Ule_orc 1 (mu d2 (fun b' => carB (p1 kb) b'))); 
      [ apply class_wretract | | ]; intro Heq.
    (* case [d2 (p1 kb) == 1] *)
    apply wretract_le with (fun k => [1-] not_first_repr carBC p k * mu d' (carBC (p k))).
      intro k; rewrite (Uge_one_eq _ Heq), Udiv_one_strong.
      apply (cover_elim (carB_prop (p1 kb)) (p1 k)); [ auto | | ]; 
        intros (H',H''); rewrite H''; repeat Usimpl; trivial.
        rewrite H'; unfold p1; rewrite <-surjective_pairing; auto.
    apply wretract_le with (coeff carBC p d').
      intro k; apply (cover_elim (cover_not_first_repr _ _ carBC_prop p) k); 
        [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl.
        rewrite (coeff_first_repr _ carBC_prop Hp _ H5); trivial.
        trivial.
    apply (wretract_coeff _ carBC_prop p d').
    (* case [d2 (p1 kb) < 1] *)
    apply wretract_le with (fun kc  => ([1-] not_first_repr carBC p kc * 
      carB (p1 kb) (p1 kc) * mu d' (carBC (p1 kb, snd (p kc)))) /
       mu d2 (fun b' => carB (p1 kb) b')).
      intros k.
      apply Oeq_le; symmetry; apply Umult_div_assoc.
      rewrite <-(le_p1 Hd' (fun b' => carB (p1 kb) b'));
        simpl; unfold carBC, carProd; auto.
    apply (wretract_Udiv _ Heq).
    intro n.
    rewrite le_lub.
    transitivity (serie (fun k => [1-] not_first_repr carBC p k *
      ((mu d') (carBC (p k)) * carB (p1 kb) (p1 k)))).
      apply lub_le_compat; refine (ford_le_intro _); intro; apply sigma_le_compat; intros.
      apply (cover_elim (carB_prop (p1 kb)) (p1 k)); [ auto | | ]; 
        intros (H',H''); rewrite H''; repeat Usimpl; trivial.
        rewrite H'; unfold p1; rewrite <-surjective_pairing; trivial.
    rewrite <-(le_p1 Hd' (fun b' => carB (p1 kb) b')); simpl.
    rewrite (mu_is_Discrete _ carBC_prop (mkDiscr Hp)); simpl.
    rewrite (discr_distr_simpl _ carBC_prop Hp) with (f:=fun bc =>
      carB (p1 kb) (fst bc)); trivial.
  (* Bound the inner serie by [1] *)
  rewrite serie_prod_maj.
  (* Split the serie in two *)
  set (PR:= fun b => B2U (Uleb (lam ** mu (Msnd d) (fun b' => carB b b')) 
    (mu d2 (fun b' => carB b b')))).
  transitivity (serie (fun k => 
       [1-] not_first_repr carB p1 k * PR (p1 k) * 
       mu d2 (fun b' => carB (p1 k) b') -
       lam ** ([1-] not_first_repr carB p1 k * PR (p1 k) * 
         mu (Msnd d) (fun b' => carB (p1 k) b')))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p1) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl; trivial.
      unfold PR, B2U, F.
      match goal with |- context [Uleb ?X1 ?X2] => 
        generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; repeat Usimpl;
          [ trivial | apply (Uminus_le_zero _ _ (Ult_le  Heq)) ]
      end.
  rewrite <-serie_minus_eq.
    Focus 2.
    intros k. 
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p1) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat (Usimpl || multRU_simpl); trivial.
    unfold PR, B2U, F.
    match goal with |- context [Uleb ?X1 ?X2] => 
      generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; 
        repeat (Usimpl || multRU_simpl); trivial
    end.
    Focus 2.
    apply wretract_le with (fun k => [1-] not_first_repr carB p1 k *
      mu d2 (fun b' => carB (p1 k) b')); [ auto | ].
    intro n.
    rewrite <-(mu_stable_mult d2 ([1-] _)).
    transitivity ([1-] (sigma (fun k => mu d2
      (fmult ([1-] not_first_repr carB p1 k) (fun b' => carB (p1 k) b'))) n));
      [ | Usimpl; apply sigma_le_compat; intros k _; apply (mu_stable_mult d2) ].
    rewrite <-mu_sigma_eq.
      (* 1st subg *)
      apply mu_fplusok.
      unfold fplusok, fmult, finv, sigma_fun; intro b; fold (p1 n).
      apply (cover_elim (carB_prop (p1 n)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p1) n); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'; fold (p1 k').
        apply (cover_elim (carB_prop (p1 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
      (* 2nd subg *) 
      intros b k Hk; unfold fmult; fold (p1 k).
      apply (cover_elim (carB_prop (p1 k)) b); [ auto | | ]; intros [H4 H5].
        rewrite H5; Usimpl; trivial.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p1) k); 
            [auto | | ]; intros [H4' H5']; rewrite H5'; repeat Usimpl; trivial.
        rewrite sigma_zero; [ Usimpl; trivial | ].
        intros k' Hk'; fold (p1 k').
        apply (cover_elim (carB_prop (p1 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  (* Push the factors multiplying the distributions inside the measured functions and
     the [lam] term outside the rightmost serie *)
  transitivity (serie (fun k => mu d2 (fmult ([1-] not_first_repr carB p1 k * PR (p1 k))
    (fun b => carB (p1 k) b))) -
            lam ** serie (fun k => mu (Msnd d) (fmult ([1-] not_first_repr carB p1 k * PR (p1 k))
    (fun b => carB (p1 k) b)))).
    apply Uminus_le_compat; [ | rewrite (multRU_serie _ Hlam); 
      apply multRU_le_compat; [ fourier | apply Rle_refl | ] ];
        apply serie_le_compat; intro k; apply  mu_stable_mult.
  (* Push the series inside the function being measured by [d2] and [Msnd d] *)
  assert (Haux: forall b, wretract (fun k => fmult ([1-] not_first_repr carB p1 k * PR (p1 k)) 
    (fun b' => carB (p1 k) b') b)).
      intro b. 
      apply wretract_le with  (fun k => carB (p1 k) b * [1-] not_first_repr carB p1 k);
        [ unfold fmult; intro k; rewrite Umult_sym, Umult_assoc; trivial | ].
      intro k.
      apply (cover_elim (carB_prop (p1 k)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p1) k); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'.
        apply (cover_elim (carB_prop (p1 k')) b); auto; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  rewrite <-2 (mu_serie_eq _ _ Haux).
  (* Use the hypothesis about the distance between [d2] and [Msnd d] 
     to conclude *)
  match goal with |- fmonot _ ?PP' - _ <= _  => set (FF:=PP') end.
  rewrite <-(le_d Hd (fzero _) FF), <-max_le_left; apply Ule_plus_left.
 Qed.


 Lemma dd'_distance: forall (f : A -O-> U) (g : C -O-> U),
  max (d_expr (Mfst dd') d1 (lam' * lam)%R f f) 
      (d_expr (Msnd dd') d3 (lam' * lam)%R g g) <=
  max (ep' + lam' ** ep) (ep + lam ** ep').
 Proof.
  intros; apply max_le.
  (* 1st ineq *)
  rewrite (@d_expr_trans_aux _ _ _  (Mfst dd') (Mfst d) d1 lam' lam f f f 
    (le_lam Hd') (le_lam Hd)).
  apply max_le_compat; apply Uplus_le_compat.
    apply dist_l_aux.
    refine (multRU_le_compat _ _ _ (Rle_refl _) _).
      pose proof (le_lam Hd'); fourier.
      rewrite <-(le_d Hd f (fzero _)), <-max_le_right; trivial.
    rewrite <-(le_d Hd f (fzero _)), <-max_le_right; trivial.
    refine (multRU_le_compat _ _ _ (Rle_refl _) _).
      pose proof (le_lam Hd); fourier.
      apply dist_l_aux.
  (* 2nd ineq *)
  rewrite Rmult_comm, max_comm.
  rewrite (@d_expr_trans_aux _ _ _  (Msnd dd') (Msnd d') d3 lam lam' g g g
    (le_lam Hd) (le_lam Hd')).
  apply max_le_compat; apply Uplus_le_compat.
    apply dist_r_aux.
    refine (multRU_le_compat _ _ _ (Rle_refl _) _).
      pose proof (le_lam Hd); fourier.
      rewrite <-(le_d Hd' (fzero _) g), <-max_le_left; trivial.
    rewrite <-(le_d Hd' (fzero _) g), <-max_le_left; trivial.
    refine (multRU_le_compat _ _ _ (Rle_refl _) _).
      pose proof (le_lam Hd'); fourier.
      apply dist_r_aux.
 Qed.


 Lemma le_lift_trans_discr: le_lift S dd' d1 d3 (lam * lam') 
    (max (ep + lam ** ep') (ep' + lam' ** ep)).
 Proof.
  constructor.
    (* [1 <= lam] *) 
    rewrite <-(Rmult_1_r 1).
    apply Rmult_le_compat; auto with real;
     [ apply (le_lam Hd) | apply (le_lam Hd') ].
    (* distance *)
    intros; rewrite Rmult_comm, (max_comm (_ + _)); apply dd'_distance.
    (* range *)
    apply dd'_range.
    (* projections *)
    intro f; rewrite (Mfst_dd'_le_Mfst_d  f); apply (le_p1 Hd).
    intro f; rewrite (Msnd_dd'_le_Msnd_d' f); apply (le_p2 Hd').
 Qed.


End LIFT_TRANS.


Section DISCR_LIFT.

 Lemma Ueq_zero_dec: forall (a:U), sumbool (a == 0) (~ a == 0).
 Proof.
  intro a.
  case_eq (Uleb a 0); intro H; 
    [ apply Uleb_correct in H | apply Uleb_complete in H ].
  left; split; trivial.
  right; intro H'; rewrite H' in H; auto.
 Qed.


Section Discr_lift_Asym_l.

 Variable A B : Type.

 Variable FA: A -> B.

 Variable d:Distr (A * B).
 Variable d1:Distr A.
 Variable d2:Distr B.

 Variable lam:R.

 Variable carA: A  -> A -O-> U.
 Variable carB: B  -> B -O-> U.

 Hypothesis carA_prop:  forall a:A , cover (eq a) (carA a).
 Hypothesis carB_prop:  forall b:B , cover (eq b) (carB b).

 Let  carAB: A*B -> MF (A*B) := carProd carA carB.
 Let carAB_prop: forall ab, cover (fun x => ab = x) (carAB ab). 
 Proof.
  apply (cover_eq_prod _ _ carA_prop carB_prop).
 Qed.

 Let Dfst (a1:A) : Distr (A*B) := distr_mult (fun q => carA a1 (fst q)) d.

 Lemma Dfst_le : forall a1, 
  mu (Dfst a1) (fone _) <=  mu d (fun q => carA a1 (fst q)).
 Proof.
  intro; unfold Dfst; simpl;
    apply (mu_monotonic d); intro; auto. 
 Qed.

 Definition dl_restr : A -> Distr (A*B) := 
  fun a1 => distr_div _ _ (Dfst_le a1).

 Definition dl: Distr (A * B) := Mlet d1 
   (fun a1 =>  if Ueq_zero_dec (mu (Mfst d) (carA a1)) then Munit (a1,FA a1) else
     dl_restr a1).

 Lemma is_Discrete_dl:
   is_Discrete d ->
   is_Discrete d1 -> 
   is_Discrete dl.
 Proof.
   unfold dl; intros Hd Hd1.
   apply (is_Discrete_Mlet _ Hd1).
   intro a; destruct (Ueq_zero_dec (mu (Mfst d) (carA a))).
    apply is_Discrete_Munit.
    apply (is_Discrete_distr_div _ _ (is_Discrete_distr_mult _ Hd)).
 Qed.

 Lemma Mfst_dl: is_Discrete d1 -> Mfst dl == d1.
 Proof.
  intro Hd1.
  apply eq_distr_intro; intro f; simpl.
  set (p2 := D_points Hd1).
  set (c2 := coeff carA p2 d1).
  rewrite 2 (mu_is_Discrete _ carA_prop Hd1); 
    simpl; fold p2 c2.
  apply serie_eq_compat; intro k.
  match goal with |- context [if ?C then _ else _] => destruct C as [H' | H'] end; simpl.
    unfold fconj.
    simpl.
    
    trivial.
    transitivity (c2 k * f (p2 k) * (mu d (fun a1b1 => carA (p2 k) (fst a1b1)) /
      mu d (fun q => carA (p2 k) (fst q)))).
      rewrite <-Umult_assoc; Usimpl.
      rewrite <-(Umult_div_assoc _ _ _ (Ole_refl _)); apply Udiv_eq_compat_left.
      rewrite <-(mu_stable_mult d (f (p2 k))).
      apply (mu_stable_eq d); unfold fmult; refine (ford_eq_intro _); intro a1b1.
      rewrite Umult_sym.
      apply (cover_elim (carA_prop (p2 k)) (fst a1b1)); [ auto | | ]; 
        intros [H4 H5]; rewrite H5; repeat Usimpl; [ | rewrite H4 ]; trivial.
      rewrite (Udiv_refl (neq_sym H')); auto.
 Qed.

 Lemma d_le_dl_aux: forall ab,
  mu (Mlet d1 dl_restr) (carAB ab) ==
  mu d1 (fun a => carA a (fst ab)) *
   (mu d (carAB ab) / mu d (fun ab' => carA (fst ab') (fst ab))).
 Proof.
  intros; simpl.
  transitivity (mu d1 (fun a => mu d (fmult (carA a (fst ab)) (carAB ab)) /
    mu d (fun ab' => carA a (fst ab')))).
    apply (mu_stable_eq d1); refine (ford_eq_intro _); intro a.
    apply Udiv_eq_compat_left.
    unfold fmult; apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab'.
    apply (cover_elim (carAB_prop ab) ab'); [ auto | | ]; intros [H6 H7];
      [ rewrite H7; repeat Usimpl | rewrite H6 ]; trivial.
  transitivity (mu d1 (fun a => carA a (fst ab) * mu d (carAB ab) /        
    mu d (fun ab' => carA (fst ab') (fst ab)))).
    apply (mu_stable_eq d1); refine (ford_eq_intro _); intro a.
    rewrite (mu_stable_mult d (carA a (fst ab))).
    apply (cover_elim (carA_prop a) (fst ab)); [ auto | | ]; intros [H6 H7].
      rewrite H7; repeat Usimpl; rewrite 2 (Udiv_zero_eq _ (Oeq_refl _)); trivial.
      apply Udiv_eq_compat_right.
      apply mu_stable_eq; refine (ford_eq_intro _); intro ab'.
      rewrite H6; apply (BaseDef.carA_sym _ carA_prop).
  rewrite <-(mu_stable_mult_right d1).
  apply (mu_stable_eq d1); refine (ford_eq_intro _); intro a.
  apply Umult_div_assoc. 
  unfold carAB, carProd; apply (mu_monotonic d); intro; 
    rewrite (BaseDef.carA_sym _ carA_prop);  auto.
 Qed.

 Lemma d_le_dl:
  is_Discrete d ->
  is_Discrete d1 ->
  (Mfst d <= d1) ->
  d <= dl.
 Proof.
  intros d_discr d1_discr Hdd1 f.
  assert (H': is_Discrete (Mlet d1 dl_restr)).
    apply (is_Discrete_Mlet _ d1_discr).
    intro a1; apply (is_Discrete_distr_div _ _ 
      (is_Discrete_distr_mult _ d_discr)).
  pose proof (disc_eqpoint_l d_discr H') as Hd.
  pose proof (disc_eqpoint_r d_discr H') as Hd'.
  pose (p:=parity_split (D_points d_discr) (D_points H'));
    fold p in Hd, Hd'.
  transitivity (mu (Mlet d1 dl_restr) f).
  (* left ineq *)
  rewrite (mu_is_Discrete _ carAB_prop (mkDiscr Hd)),
    (mu_is_Discrete _ carAB_prop (mkDiscr Hd')); simpl.
  apply serie_le_compat; intro k.
  apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
    [auto | | ]; intros [H4 H5].
    (* first repr *)
    rewrite (coeff_first_repr _ carAB_prop Hd _ H5),
      (coeff_first_repr _ carAB_prop Hd' _ H5).
    apply Umult_le_compat_left.
    rewrite d_le_dl_aux.
    assert (Haux: mu d (carAB (p k)) <= mu d (fun ab => carA (fst ab) (fst (p k))))
        by (unfold carAB, carProd; apply mu_monotonic; intro;
          rewrite (BaseDef.carA_sym _ carA_prop);  auto).
    apply (Ueq_orc 0  (mu d (fun ab => carA (fst ab) (fst (p k)))));
        [ auto | | ]; intros.
      transitivity (@D0 U); [ rewrite H; apply Haux | trivial ].
      rewrite <-(Umult_div_assoc _ _ _ Haux), Umult_sym.
      apply (Umult_div_le_left _ _ H).
      apply Umult_le_compat_right.
      apply (Hdd1 (fun a : A => carA a (fst (p k)))).
    (* not first repr *)
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
  (* right ineq *)
  unfold dl; repeat rewrite Mlet_simpl.
  apply mu_monotonic; intro a.
  destruct (Ueq_zero_dec ((mu (Mfst d)) (carA a))) as [ H'' | ].
    simpl in *.
    rewrite Udiv_zero_eq; trivial.
    symmetry; apply Ule_zero_eq; rewrite <-H''; auto.
    trivial.
 Qed.

 Lemma dl_range: forall S,
   range S d ->
   (forall a, S (a,FA a)) ->
   range S dl.
 Proof.
   intros S Hd HFA f Hf; unfold dl.
   rewrite Mlet_simpl, <-(mu_zero d1).
   apply mu_stable_eq; unfold fzero; 
     refine (ford_eq_intro _); intro a.
   match goal with |- context [if Ueq_zero_dec ?C then _ else _] => 
     destruct (Ueq_zero_dec C) as [H | H ] end; simpl.
     auto.
     symmetry; apply Udiv_zero_eq.
     apply Hd; intros ab Hab.
     rewrite <-(Hf _ Hab); auto.
 Qed.

 Lemma le_dist_d_dl: forall ep, 
  (1 <= lam)%R ->
  is_Discrete dl ->
  (d <= dl) -> 
  le_dist d1 (Mfst d) lam ep ->
  le_dist d dl lam ep.
 Proof.
  intros ep Hlam dl_discr Hddl Hdist.
  set (P1 := fun (a:A * B) => Uleb (lam ** mu d (carAB a)) 
    (mu dl (carAB a))).
  set (P2 := fun (a:A) => 
    if Ueq_zero_dec (mu (Mfst d) (carA a)) then true else false).
  set (P3 := fun (a:A) => Uleb  
    (lam ** mu d (fun ab => carA a (fst ab))) (mu d1 (carA a))).  
  set (M1:=charfun P1).

  (* Apply lemma [le_dist_discr_ub_le] to bound the distance *)
  eapply le_dist_weaken_ep; [ | apply (le_dist_discr_ub_le _ 
    carAB_prop Hlam (D_Discr dl_discr) Hddl) ].
  change (mu dl M1 - lam ** mu d M1 <= ep).

  (* Split distributions by a case analysis on [P2] *)
  rewrite (mu_restr_split dl (fun ab => P2 (fst ab)) M1), (mu_restr_split d (fun ab => P2 (fst ab)) M1).
  rewrite <-(multRU_distr_plus_l _ _ Hlam), Uplus_minus_perm_assoc.
  rewrite Uplus_sym.

  (* Discretize the distributions *)
  destruct dl_discr as (p,dl_discr).
  pose proof (enum_le dl_discr Hddl) as d_discr.
  rewrite 2 (mu_is_Discrete _ carAB_prop (mkDiscr d_discr)),
    2 (mu_is_Discrete _ carAB_prop (mkDiscr dl_discr)); simpl.
  rewrite 2 (discr_distr_simpl _ carAB_prop d_discr),
    2 (discr_distr_simpl _ carAB_prop dl_discr).

  (* Simplify [dl] definition in each case and merge 
     the first pair of series *)
  rewrite <- (multRU_serie _ Hlam).
  rewrite serie_minus_le; unfold fminus.
  match goal with |- _ + (_ - ?X) <= _ => 
    transitivity ( serie (fun k  => [1-] not_first_repr carAB p k *
    ((mu d1 (carA (fst (p k))) - lam ** mu (Mfst d) (carA (fst (p k)))) *
    restr (negP (fun ab => P2 (fst ab))) M1 (p k) * (mu d (carAB (p k)) / mu (Mfst d) (carA (fst (p k)))))) + 
    (serie (fun k => [1-] not_first_repr carAB p k *
       (mu d1 (carA (fst (p k))) * carB (snd (p k))  (FA (fst (p k))) * restr (fun ab => P2 (fst ab)) M1 (p k)))- X))
  end.
  apply Uplus_le_compat.
    (* Left term *)
    apply serie_le_compat; intro k.
    rewrite <-(Umult_sym (mu d _ * _)), <-(Umult_multRU_assoc _ _ Hlam),
      (Umult_sym (_ ** _)), <-Uminus_distr_right; Usimpl.
    unfold negP, negb, P2, restr, fone;     
    match goal with |- context [if Ueq_zero_dec ?C then _ else _] => 
      destruct (Ueq_zero_dec C) as [H | H ]; [ repeat Usimpl; trivial | ]
    end.
    rewrite <-(Umult_multRU_assoc _ _ Hlam), <-Uminus_distr_left,
      <-Umult_assoc, (Umult_sym (M1 _)), Umult_assoc; Usimpl.
    rewrite Uminus_distr_left; apply Uminus_le_compat.
      (* Left expr *)
      rewrite <-mu_stable_mult_right.
      unfold dl; simpl.
      apply (mu_monotonic d1); intro a1.
      match goal with |- context [if ?C then _ else _] => 
        destruct C as [H1 | H1 ] 
      end; unfold carAB, carProd; simpl.
        (* 1st case *)
        unfold carAB; simpl.
        apply (cover_elim (carA_prop (fst (p k))) a1); [auto | | ]; intros [H2 H3];
          [ rewrite H3; repeat Usimpl; trivial | rewrite <-H2 in H1; elim (H H1) ].
        (* 2nd case *)
        apply (cover_elim (carA_prop (fst (p k))) a1); [auto | | ]; 
          intros [H2 H3]; rewrite H3; Usimpl.
          apply Udiv_zero_eq; rewrite <-(mu_zero d).
          apply (mu_stable_eq d); unfold fzero, carAB; refine (ford_eq_intro _); 
            intros (a,b); simpl.
           apply (cover_elim (carA_prop a1) a); [auto | | ]; intros [H2' H3'];
            [ rewrite H3'; Usimpl | rewrite <-H2', H3; repeat Usimpl]; trivial.
          rewrite H2; apply Udiv_le_compat_left; auto.
      (* Right expr *)
      rewrite (Umult_multRU_assoc _ _ Hlam).
      apply multRU_le_compat; [ fourier | apply Rle_refl | apply Umult_div_le ].
    (* Right term *)
    apply Uminus_le_compat_left.
    apply serie_le_compat; intro k.
    Usimpl.
    unfold restr, P2;
    match goal with |- context [if Ueq_zero_dec ?C then _ else _] => 
      destruct (Ueq_zero_dec C) as [H | _ ]; [ | repeat Usimpl; trivial ]
    end.
    Usimpl.
    rewrite <-mu_stable_mult_right.
    unfold dl; simpl.
    apply (mu_monotonic d1); intro a1.
    match goal with |- context [if ?C then _ else _] => 
      destruct C as [H1 | H1 ] 
    end; unfold carAB, carProd; simpl.
      (* 1st case *)
      apply (cover_elim (carA_prop (fst (p k))) a1); [auto | | ]; intros [H2 H3];
        [ rewrite H3; repeat Usimpl | rewrite H2 ]; trivial.
      (* 2nd case *)
      rewrite Udiv_zero_eq; trivial. 
      split; trivial; rewrite <-H; simpl.
      apply (mu_monotonic d); intros (a,b); simpl.
      rewrite Ule_mult_left; auto.

  (* Rewrite the series as two nested series *)
  unfold carAB at  1 3 4;
   rewrite (sigma_prod_split_r _ _ p carA_prop 
    carB_prop (fun ab => mu d1 (carA (fst ab)) * 
      carB (snd ab) (FA (fst ab)) * restr (fun ab => P2 (fst ab)) M1 ab)),
   (sigma_prod_split_r _ _ p carA_prop carB_prop (fun ab =>
     (mu d1 (carA (fst ab)) - lam ** mu (Mfst d) (carA (fst ab))) *
       restr (negP (fun ab':A * B => P2 (fst ab'))) M1 ab *
       (mu d (carAB ab) / mu (Mfst d) (carA (fst ab))))),
   (sigma_prod_split_r _ _ p carA_prop carB_prop (fun ab =>
     mu d (carAB ab) * restr (fun ab':A * B => P2 (fst ab')) M1 ab)); simpl.
   

  (* Push some factors outside the inner series *)
  match goal with |- _ + (_ - ?X) <= _ => set (AUX:=X) end.
  transitivity
  (serie
     (fun ka : nat =>
      ([1-] not_first_repr carA (fun k => fst (p k)) ka) *
      (mu d1 (carA (fst (p ka))) - 
       lam ** mu d (fun ab:A * B => carA (fst (p ka)) (fst ab))) *
      (charfun (negP P2) (fst (p ka))) *
      serie
        (fun kb : nat =>
         [1-] not_first_repr (carProd carA carB) p kb *
         carA (fst (p kb)) (fst (p ka)) *
         (charfun P1 (fst (p ka), snd (p kb))) *
         (mu d (carAB (fst (p ka), snd (p kb))) /
           mu d (fun ab:A * B => carA (fst (p ka)) (fst ab))))) +
    ((serie (fun ka : nat =>
      [1-] not_first_repr carA (fun k => fst (p k)) ka *
      (mu d1 (carA (fst (p ka))) *
      (charfun P2 (fst (p ka))) *
      serie 
        (fun kb : nat =>
         [1-] not_first_repr (carProd carA carB) p kb *
         carA (fst (p kb)) (fst (p ka)) *
         (carB (snd (p kb)) (FA (fst (p ka))) *
         (charfun P1 (fst (p ka), snd (p kb)))))))) 
    - AUX)).
  apply Uplus_le_compat; [ | apply Uminus_le_compat ].
  (* 1st term *)
  apply serie_le_compat; intro ka.
  rewrite <- 2 Umult_assoc; Usimpl.
  rewrite Umult_assoc, <-serie_mult.
  apply serie_le_compat; intro kb.
  unfold M1; rewrite (ford_eq_elim (restr_charfun 
    (fun ab:A * B => (negP P2) (fst ab)) P1)); unfold Fmult; simpl.
  unfold charfun at 1 3, restr, fone; simpl.
  match goal with |- ?A * ?B * (?C * (?D * ?E) * ?F ) <= 
    ?C * ?D * (?A * ?B *  ?E * ?F) => 
    rewrite  <-(Umult_assoc C), <-(Umult_assoc D),
      (Umult_sym D), (Umult_sym C), <-(Umult_assoc (E * F)),
      Umult_assoc, Umult_sym, (Umult_sym D); auto
  end.
  set (D:= mu d (fun ab:A * B => carA (fst (p ka)) (fst ab))).
  set (a':= fst (p ka)).
  apply (Ule_orc 1 D); 
      [ apply class_wretract | | ]; intro Heq.
    (* case [D == 1] *)
    apply wretract_le with (fun kb => [1-] not_first_repr carAB p kb *
      carA (fst (p kb)) a' * mu (Msnd d) (carB (snd (p kb)))).
      intro kb; rewrite (Uge_one_eq _ Heq), Udiv_one_strong. 
      rewrite <-Umult_assoc; apply Umult_le_compat_right.
      rewrite Ule_mult_left.
      simpl; apply (mu_monotonic d); intros (a,b); unfold carAB, carProd; simpl; trivial.
    apply (wretract_prod_eq_proj1 _ _ _ _ carA_prop carB_prop).
    (* case [D < 1] *)
    apply wretract_le with (fun kb => ([1-] not_first_repr carAB p kb * 
       carA (fst (p kb)) a' * mu d (carAB (a', snd (p kb)))) / D).
      intro k.
      rewrite Ule_mult_right with (y:=charfun P1 (a', snd (p k))).
      rewrite <-Umult_div_assoc; trivial.
      unfold D; apply (mu_monotonic d); intros (a,b); unfold carAB, carProd; simpl; trivial.
    apply (wretract_Udiv _ Heq).
    intro n.
    unfold D.
    rewrite (mu_is_Discrete _ carAB_prop (mkDiscr d_discr)); simpl.
    rewrite (discr_distr_simpl _ carAB_prop d_discr) with (f:=fun ab =>
      carA (fst (p ka)) (fst ab)).
    rewrite le_lub; apply serie_le_compat; intro k.
    rewrite <-Umult_assoc, (Umult_sym (carA _ _)); Usimpl; fold a'.
    apply (cover_elim (carA_prop (fst (p k))) a'); [ auto | | ]; intros (H',H'').
        rewrite H''; repeat Usimpl; trivial.
        rewrite <-H' at 1; rewrite <-surjective_pairing, (carA_sym _ carA_prop); trivial.
  (* 2nd term *)
  apply serie_le_compat; intro ka.
  Usimpl.
  rewrite <-serie_mult.
  apply serie_le_compat; intro kb.
  unfold M1; rewrite (ford_eq_elim (restr_charfun 
    (fun ab:A * B => P2 (fst ab)) P1)); unfold Fmult; simpl.
  unfold charfun at 1 3, restr, fone; simpl.
  match goal with |- ?A * ?B * (?C * ?D * (?E * ?F)) <= 
    ?C * ?E * (?A * ?B * (?D * ?F)) => 
  rewrite (Umult_sym (C * E)), <-(Umult_assoc (A * B)); Usimpl;
  rewrite (Umult_sym C E), <-(Umult_assoc D), (Umult_assoc F),
    (Umult_sym F  E), (Umult_sym (E * F)), (Umult_assoc D); auto
  end.
  apply wretract_le with  (fun k =>  [1-] not_first_repr carAB p k *
    carAB (p k) (fst (p ka),FA (fst (p ka)))).
    intro k.
    rewrite Ule_mult_right with (y:=charfun P1 (fst (p ka), snd (p k))).
    rewrite <-Umult_assoc; apply Ole_refl.
  apply (enum_wretract_eq _ _ carAB_prop).
  (* 3rd term *)
  trivial.

  (* Bound each of the inner series by [1] *)
  transitivity 
    (serie (fun ka  =>
    ([1-] not_first_repr carA (fun k => fst (p k)) ka) *
    (mu d1 (carA (fst (p ka))) - lam ** 
      mu d (fun ab:A * B => carA (fst (p ka)) (fst ab))) *
    charfun (negP P2) (fst (p ka))) +
    (serie (fun ka  =>
       [1-] not_first_repr carA (fun k => fst (p k)) ka *
       (mu d1 (carA (fst (p ka))) * charfun P2 (fst (p ka)))) - AUX)).
  apply Uplus_le_compat; [ | apply Uminus_le_compat ].
  (* 1st term *)
  apply serie_le_compat; intro ka.
  rewrite (Unit (serie _)); Usimpl; trivial.
  (* 2nd term *)
  apply serie_le_compat; intro ka.
  rewrite (Unit (serie _)); Usimpl; trivial.
  (* 3rd term *)
  trivial.

  (* Write the 3rd series in a convinient way *) 
  setoid_replace AUX with (lam ** serie (fun ka  =>
    [1-] not_first_repr carA (fun k => fst (p k)) ka *
    mu d (fun ab:A * B => carA (fst (p ka)) (fst ab)) *
    charfun P2 (fst (p ka)))). 
  Focus 2.
  unfold AUX.
  apply multRU_eq_compat; trivial.
  apply serie_eq_compat; intro ka.
  rewrite <-Umult_assoc; Usimpl.
  transitivity (@D0 U).
    apply serie_zero. 
    intro kb; unfold M1, restr, fone, P2.
    match goal with |- context [if Ueq_zero_dec ?C then _ else _] => 
      destruct (Ueq_zero_dec C) as [H' | _ ]; [ | repeat Usimpl; trivial ]
    end.
    apply Umult_zero_right_eq, Umult_zero_left_eq.
    split; trivial; rewrite <-H'; simpl.
    apply (mu_monotonic d); intros (a,b); unfold carAB, carProd; simpl; auto.
    unfold charfun, restr, fone, P2.
    match goal with |- context [if Ueq_zero_dec ?C then _ else _] => 
      destruct (Ueq_zero_dec C) as [H' | _ ]; repeat Usimpl; trivial
    end.
    symmetry; apply H'.

  (* Merge the three series and eliminate the case analysis over [P2] *)
  rewrite <-(multRU_serie _ Hlam), serie_minus_le, <-serie_plus.
  transitivity (serie (fun ka  =>
    [1-] not_first_repr carA (fun k => fst (p k)) ka *
    (mu d1 (carA (fst (p ka))) - lam ** mu d 
      (fun ab : A * B => carA (fst (p ka)) (fst ab))))). 
    apply serie_le_compat; intro k; unfold fminus.
    rewrite <-(Umult_sym (mu d _)), <-(Umult_assoc (mu d _)),
      <-(Umult_multRU_assoc _ _ Hlam), (Umult_assoc (_ ** _)), 
      (Umult_sym (_ ** _)).
    unfold charfun, restr, negP, fone;
    case (P2 (fst (p k))); simpl; repeat Usimpl; trivial.
    rewrite <-Uminus_distr_right; trivial.

  (* Sum only over those [a]'s satisfying [P3] and split
     the serie into two series *)
  transitivity (serie (fun ka =>
      [1-] not_first_repr carA (fun k : nat => fst (p k)) ka *
      (mu d1 (carA (fst (p ka))) - lam ** mu d 
        (fun ab : A * B => carA (fst (p ka)) (fst ab))) *
      charfun P3 (fst (p ka)) )). 
    apply serie_le_compat; intro k.
    unfold charfun, restr, fone, P3;
    match goal with |- context [if ?C then _ else _] => 
        case_eq C; intros; repeat Usimpl; trivial
    end.
    rewrite (Uminus_le_zero _ _ (Ult_le (Uleb_complete H))); Usimpl; trivial.
  transitivity (serie (fun ka =>
    [1-] not_first_repr carA (fun k : nat => fst (p k)) ka *
    mu d1 (carA (fst (p ka))) * charfun P3 (fst (p ka)) -
    ([1-] not_first_repr carA (fun k : nat => fst (p k)) ka) *
    (lam ** mu d (fun ab => carA (fst (p ka)) (fst ab))) * 
    charfun P3 (fst (p ka)))).
  apply serie_le_compat; intro k.
  rewrite Uminus_distr_right, Uminus_distr_left; trivial.
  rewrite <-serie_minus_eq.
  Focus 2.
    intros.
    rewrite <- 2 Umult_assoc; apply Umult_le_compat_right.
    unfold charfun, restr, fone, P3.
    match goal with |- context [if ?C then _ else _] => 
      case_eq C; intro; repeat Usimpl; auto using Uleb_correct
    end.
  Focus 2.
  apply wretract_le with (fun k => [1-] not_first_repr carA (fun k' => fst (p k')) k *
    mu d1 (carA (fst (p k)))); [ intro k; apply Ule_mult_right | ].
  apply wretract_le with (coeff carA (fun k' => fst (p k')) d1).
    intro k; apply (cover_elim (cover_not_first_repr _ _ carA_prop (fun k' => fst (p k'))) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl.
      unfold coeff; rewrite H5; repeat Usimpl; trivial.
      trivial.
  apply (wretract_coeff _ carA_prop  (fun k' => fst (p k')) d1).


  (* Push the serie inside the functions measured 
     by distributions [d1] and [d] respectively *)
  set (f1:= fun k a => [1-] not_first_repr carA (fun k' => fst (p k')) k *
    carA (fst (p k)) a * charfun P3 (fst (p k))).
  transitivity (mu d1 (serie_fun f1) - lam ** mu (Mfst d) (serie_fun f1)).
    apply Uminus_le_compat.
    (* left term *)
    rewrite mu_serie_eq.
    apply serie_le_compat; intro k.
    rewrite <-(mu_stable_mult d1 ([1-] _)), <-(mu_stable_mult_right d1).
    apply mu_monotonic; intro a; trivial.
    intro a; unfold f1.
    apply wretract_le with  (fun k =>  [1-] not_first_repr carA (fun k' => fst (p k')) k *
      carA (fst (p k)) a); [ auto | ].
    apply (enum_wretract_eq _ _ carA_prop).
    (* right term *)
    transitivity (lam ** serie (fun k => mu (Mfst d) (f1 k))).
    apply multRU_le_compat; [ fourier | apply Rle_refl | apply mu_serie_le].
    rewrite <-(multRU_serie _ Hlam).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ carA_prop 
      (fun k' => fst (p k'))) k); [auto | | ]; intros [_ H5]; 
         rewrite H5; repeat Usimpl.
      (* first repr *)
      unfold charfun, restr, fone, P3.
      match goal with |- context [if ?C then _ else _] => 
        case_eq C; intro H2; repeat Usimpl
      end.
        (* case [P3] *)
        apply multRU_le_compat; [ fourier | apply Rle_refl | ].
        simpl; apply (mu_monotonic d); intro a; unfold f1.
        unfold charfun, restr, fone, P3; rewrite H5, H2; repeat Usimpl; trivial.
        (* case [~P3] *)
        rewrite <-(multRU_0_r lam), <-(mu_zero (Mfst d)).
        apply multRU_le_compat; [ fourier | apply Rle_refl | ].
        apply mu_monotonic; unfold f1, fzero; intro.
        unfold charfun, restr, P3; rewrite H2; repeat Usimpl; trivial.
      (* not first repr *)
      rewrite <-(multRU_0_r lam), <-(mu_zero (Mfst d)).
      apply multRU_le_compat; [ fourier | apply Rle_refl | ].
      apply mu_monotonic; unfold f1, fzero; intro.
      rewrite H5; repeat Usimpl; trivial.

  (* Conclude *)
  rewrite <-(Hdist (serie_fun f1)); apply Ule_plus_right.
 Qed.

 
End Discr_lift_Asym_l.


Section Discr_lift_Asym_r.

 Variable A B : Type.

 Variable FB: B -> A.

 Variable d:Distr (A * B).
 Variable d1:Distr A.
 Variable d2:Distr B.

 Variable lam:R.

 Variable carA: A  -> A -O-> U.
 Variable carB: B  -> B -O-> U.

 Hypothesis carA_prop:  forall a:A , cover (eq a) (carA a).
 Hypothesis carB_prop:  forall b:B , cover (eq b) (carB b).

 Let  carAB: A*B -> MF (A*B) := carProd carA carB.
 Let carAB_prop: forall ab, cover (fun x => ab = x) (carAB ab). 
 Proof.
  apply (cover_eq_prod _ _ carA_prop carB_prop).
 Qed.

 Definition dr : Distr (A * B) := Mswap (@dl B A FB
 (Mswap d) d2 carB).

 Lemma is_Discrete_dr:
   is_Discrete d ->
   is_Discrete d2 -> 
   is_Discrete dr.
 Proof.
   intros Hd Hd2.
   apply Mswap_is_Discrete_inv. 
   eapply is_Discrete_eq_compat; [ symmetry; apply Mswap_Mswap | ].
   apply is_Discrete_dl.
     apply Mswap_is_Discrete_inv. 
     eapply is_Discrete_eq_compat; [ symmetry; apply Mswap_Mswap | apply Hd ].
     trivial.
 Qed.

 Lemma Msnd_dr: is_Discrete d2 -> Msnd dr == d2.
 Proof.
  intros Hd2. 
  rewrite <-(Mfst_dl FB (Mswap d) _ carB_prop Hd2).
  unfold dr; apply Mswap_snd.
 Qed.

 Lemma d_le_dr: 
  is_Discrete d ->
  is_Discrete d2 ->
  (Msnd d <= d2) ->
  d <= dr.
 Proof.
  intros Hd Hd2 Hdd2.
  assert (H: is_Discrete (Mswap d)) by (apply (is_Discrete_Mlet _ Hd); 
    intros (a,b); simpl; apply is_Discrete_Munit).
  rewrite <-(Mswap_Mswap d), <-(Mswap_Mswap dr).
  unfold Mswap at 1 3; intro f; rewrite 2 Mlet_simpl.
  apply (d_le_dl  FB _ _ carB_prop carA_prop H Hd2).
  rewrite Mswap_fst; trivial.
 Qed.

 Lemma dr_range: forall S,
   range S d ->
   (forall b, S (FB b, b)) ->
   range S dr.
 Proof.
   intros; unfold dr.
   apply Mswap_range.
   apply dl_range.
     apply Mswap_range; apply range_weaken with (2:=H); 
       intros (a,b); simpl; trivial.
     simpl; trivial.
 Qed.

  Lemma le_dist_d_dr: forall ep, 
  (1 <= lam)%R ->
  is_Discrete dr ->
  (d <= dr) -> 
  le_dist d2 (Msnd d) lam ep ->
  le_dist d dr lam ep.
 Proof.
  intros ep Hlam Hdr Hddr Hdist.
  rewrite <-(Mswap_Mswap d), <-(Mswap_Mswap dr).
  apply le_dist_Mlet.
  unfold dr; rewrite Mswap_Mswap.
  apply (@le_dist_d_dl _ _ FB (Mswap d) d2 _ _ _ carB_prop carA_prop ep Hlam).
    apply (Mswap_is_Discrete_inv Hdr).
    apply Mswap_le_inv; rewrite Mswap_Mswap; apply Hddr.
    rewrite Mswap_fst; apply Hdist.
 Qed.

End Discr_lift_Asym_r.

 Variable A1 A2 B1 B2: Type.

 Variable R1: A1 -> B1 -> Prop.
 Variable R2: A2 -> B2 -> Prop.

 Hypothesis R1_dec: forall a1 b1, {R1 a1 b1} + {~ R1 a1 b1}.

 Variable d:Distr (A1 * B1).
 Variable d1:Distr A1.
 Variable d2:Distr B1.

 Variable F:A1 * B1 -> Distr (A2 * B2).
 Variable F1:A1 -> Distr A2.
 Variable F2:B1 -> Distr B2.

 Variable lam lam':R.
 Variable ep ep':U.
 
 Variable carA1: A1  -> A1 -O-> U.
 Variable carA2: A2  -> A2 -O-> U.
 Variable carB1: B1  -> B1 -O-> U.
 Variable carB2: B2  -> B2 -O-> U.

 Variable FAB: A1 -> B1.
 Variable FBA: B1 -> A1.

 Hypothesis carA1_prop:  forall a:A1 , cover (eq a) (carA1 a).
 Hypothesis carA2_prop:  forall a:A2 , cover (eq a) (carA2 a).
 Hypothesis carB1_prop:  forall b:B1 , cover (eq b) (carB1 b).
 Hypothesis carB2_prop:  forall b:B2 , cover (eq b) (carB2 b).

 Hypothesis F1_discr: forall a : A1, is_Discrete (F1 a).
 Hypothesis F2_discr: forall b : B1, is_Discrete (F2 b).
 Hypothesis d1_discr: is_Discrete d1.
 Hypothesis d2_discr: is_Discrete d2.


 
 Let a1_def : A1 := D_points d1_discr 0%nat.
 Let b1_def : B1 := D_points d2_discr 0%nat.
 Let a2_def : A2 := D_points (F1_discr a1_def) 0%nat.
 Let b2_def : B2 := D_points (F2_discr b1_def) 0%nat.



 Hypothesis Hlift: le_lift R1 d d1 d2 lam ep.
 Hypothesis Hlift': forall (x:A1) (y:B1), 
   R1 x y -> le_lift R2 (F (x, y)) (F1 x) (F2 y) lam' ep'.

 Let  carA1B1: A1*B1 -> MF (A1*B1) := carProd carA1 carB1.
 Lemma carA1B1_prop: forall ab, cover (fun x => ab = x) (carA1B1 ab). 
 Proof.
  apply (cover_eq_prod _ _ carA1_prop carB1_prop).
 Qed.

 Let  carA2B2: A2*B2 -> MF (A2*B2) := carProd carA2 carB2.
 Lemma carA2B2_prop: forall ab, cover (fun x => ab = x) (carA2B2 ab). 
 Proof.
  apply (cover_eq_prod _ _ carA2_prop carB2_prop).
 Qed.


 Hypothesis Hlam':  (1 <= lam')%R.

 Let dl' := dl FAB d d1 carA1.
 Let dr' := dr FBA d d2 carB1.
 Let Fl':  A1*B1 -> Distr (A2 * B2) := 
   fun a1b1 => dl (fun _ => b2_def) (F a1b1) (F1 (fst a1b1)) carA2.
 Let Fr':  A1*B1 -> Distr (A2 * B2) := 
   fun a1b1 => dr (fun _ => a2_def) (F a1b1) (F2 (snd a1b1)) carB2.


 Lemma d_discr: is_Discrete d.
 Proof.
  apply (le_lift_discr_witness _ _ carA1_prop carB1_prop d1_discr d2_discr Hlift).
 Qed.
   
 Lemma F_discr: forall a1b1,
   R1 (fst a1b1) (snd a1b1) -> is_Discrete (F a1b1). 
 Proof.
  intros (a1,b1) H; simpl.
    apply (le_lift_discr_witness _ _ carA2_prop carB2_prop 
      (F1_discr a1) (F2_discr b1) (Hlift' H)).
 Qed.

 Lemma dl'_discr: is_Discrete dl'.
 Proof.
  apply (is_Discrete_dl _ _ d_discr d1_discr).
 Qed.

 Lemma dr'_discr: is_Discrete dr'.
 Proof.
  apply (is_Discrete_dr _ _ d_discr d2_discr).
 Qed.

 Lemma Fl'_discr: forall (a1b1: A1 * B1), 
   R1 (fst a1b1) (snd a1b1) ->
   is_Discrete (Fl' a1b1).
 Proof.
  intros (a1,b1) H.
  refine (is_Discrete_dl _ _ (F_discr _ H) (F1_discr  _)).
 Qed.

 Lemma Fr'_discr: forall (a1b1: A1 * B1), 
  R1 (fst a1b1) (snd a1b1) ->
  is_Discrete (Fr' a1b1).
 Proof.
  intros (a1,b1) H.
  refine (is_Discrete_dr _ _ (F_discr _ H) (F2_discr _)).
 Qed.

 Lemma Mfst_dl'_Fl': Mfst (Mlet dl' Fl') == Mlet d1 F1.
 Proof.
  unfold Mfst; rewrite Mcomp.
  transitivity (Mlet dl' (fun a1b1 => F1 (fst a1b1))).
    apply Mlet_eq_compat; trivial; refine (ford_eq_intro _); intros;
      refine (Mfst_dl (fun _ => b2_def) _ _ carA2_prop (F1_discr _)).
  transitivity (Mlet (Mfst dl') F1); [ auto | ].
  apply Mlet_eq_compat; trivial.
  refine (Mfst_dl FAB _ _ carA1_prop d1_discr).
 Qed.

 Lemma Msnd_dr'_Fr': Msnd (Mlet dr' Fr') == Mlet d2 F2.
 Proof.
  unfold Msnd; rewrite Mcomp.
  transitivity (Mlet dr' (fun a1b1 => F2 (snd a1b1))).
    apply Mlet_eq_compat; trivial; refine (ford_eq_intro _); 
      intros; refine (Msnd_dr (fun _ => a2_def) _ _ carB2_prop (F2_discr _)).
  transitivity (Mlet (Msnd dr') F2); [ auto | ].
  apply Mlet_eq_compat; trivial.
  refine (Msnd_dr FBA _ _ carB1_prop d2_discr).
 Qed.

 Lemma le_dist_d_dl': 
  (1 <= lam)%R ->
  le_dist d dl' lam ep.
 Proof.
  intro Hlam.
  refine (le_dist_d_dl _ carA1_prop carB1_prop Hlam dl'_discr _ _); fold dl'.
    refine (d_le_dl _ _ _ carA1_prop carB1_prop  d_discr d1_discr (le_p1 Hlift)).
    intro f; rewrite <-(le_d Hlift f (fzero _)), <-max_le_right, d_expr_sym; trivial.
 Qed.

 Lemma le_dist_d_dr': 
  (1 <= lam)%R ->
  le_dist d dr' lam ep.
 Proof.
  intro Hlam.
  refine (le_dist_d_dr _ carA1_prop carB1_prop Hlam dr'_discr _ _); fold dr'.
    refine (d_le_dr _ _ _ carA1_prop carB1_prop  d_discr d2_discr (le_p2 Hlift)).
    intro f; rewrite <-(le_d Hlift (fzero _) f), <-max_le_left, d_expr_sym; trivial.
 Qed.

 Lemma le_dist_F_Fl': forall (ab:A1*B1),
  R1 (fst ab) (snd ab) ->
  le_dist (F ab) (Fl' ab) lam' ep'.
 Proof.
  intros (a1,b1) H.
  refine (le_dist_d_dl _ carA2_prop carB2_prop Hlam' (Fl'_discr _ H) _ _);
    [ fold (Fl' (a1,b1)) | ].
  refine (d_le_dl _ _ _ carA2_prop carB2_prop (F_discr _ H) (F1_discr _) _).
  refine (le_p1 (Hlift' H)).
  intro f; rewrite d_expr_sym, <-(le_d (Hlift' H) f (fzero _)), 
    <-max_le_right; trivial.
 Qed.

 Lemma le_dist_F_Fr': forall (ab:A1*B1),
  R1 (fst ab) (snd ab) ->
  le_dist (F ab) (Fr' ab) lam' ep'.
 Proof.
  intros (a1,b1) H.
  refine (le_dist_d_dr _ carA2_prop carB2_prop Hlam' (Fr'_discr _ H) _ _);
    [ fold (Fr' (a1,b1)) | ].
  refine (d_le_dr _ _ _ carA2_prop carB2_prop (F_discr _ H) (F2_discr _) _).
  refine (le_p2 (Hlift' H)).
  intro f; rewrite d_expr_sym, <-(le_d (Hlift' H) (fzero _) f), 
    <-max_le_left; trivial.
  Qed.


 Hypothesis FAB_spec: forall (a:A1), R1 a (FAB a).
 Hypothesis FBA_spec: forall (b:B1), R1 (FBA b) b.

 Lemma dl'_range_full: range (prodP R1) dl'.
 Proof.
  apply (dl_range _ _ _ (le_r Hlift) FAB_spec).
 Qed.

 Lemma dr'_range_full: range (prodP R1) dr'.
 Proof.
  apply (dr_range _ _ _ (le_r Hlift) FBA_spec).
 Qed.

 Lemma le_lift_Mlet_discr_full: 
  le_lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) (lam * lam') (ep + ep').
 Proof.
  destruct Hlift as (Hlam, Hd_dist, Hd_ran, Hp1d, Hp2d).
  assert (Haux_d: is_Discrete (Mlet d (fun a : A1 * B1 => prod_distr (Munit a) (F a)))).
    refine (is_Discrete_Mlet_range _ _ Hd_ran d_discr _ ((a1_def,b1_def),(a2_def,b2_def))).
    unfold prodP; intros (a,b); simpl; apply R1_dec.
    intros ab Hab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intros ab'; apply (is_Discrete_Mlet _ (F_discr _ Hab)). 
    intros; apply is_Discrete_Munit.
  assert (Haux_dl': is_Discrete (Mlet dl' (fun ab => prod_distr (Munit ab) (Fl' ab)))).
    refine (is_Discrete_Mlet_range _ _ dl'_range_full dl'_discr _ ((a1_def,b1_def),(a2_def,b2_def))).
    unfold prodP; intros (a,b); simpl; apply R1_dec.
    intros ab Hab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intros ab'; apply (is_Discrete_Mlet _ (Fl'_discr _ Hab)). 
    intros; apply is_Discrete_Munit.
  assert (Haux_dr': is_Discrete (Mlet dr' (fun ab => prod_distr (Munit ab) (Fr' ab)))).
    refine (is_Discrete_Mlet_range _ _ dr'_range_full dr'_discr _ ((a1_def,b1_def),(a2_def,b2_def))).
    unfold prodP; intros (a,b); simpl; apply R1_dec.
    intros ab Hab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intros ab'; apply (is_Discrete_Mlet _ (Fr'_discr _ Hab)). 
    intros; apply is_Discrete_Munit.
  constructor.
  transitivity (1 * 1)%R; auto with real.
  (* distance *)
  intros f g.
  apply max_le.
    rewrite <-Mfst_dl'_Fl'.
    apply le_dist_Mlet; clear f g.
    refine (le_dist_Mlet_discr F Fl' Hlam Hlam' _ _ carA1B1_prop 
      carA2B2_prop Haux_d Haux_dl' Hd_ran dl'_range_full _ _).
      apply (le_dist_d_dl' Hlam).
      apply le_dist_F_Fl'.
    rewrite <- Msnd_dr'_Fr'.
    apply le_dist_Mlet; clear f g.
    refine (le_dist_Mlet_discr F Fr' Hlam Hlam' _ _ carA1B1_prop 
      carA2B2_prop Haux_d Haux_dr' Hd_ran dr'_range_full _ _).
      apply (le_dist_d_dr' Hlam).
      apply le_dist_F_Fr'.
  (* range *)
  apply range_Mlet with (prodP R1).
  exact Hd_ran. 
  intros (a,b) H'. apply (le_r (Hlift' H')).    
  (* projections *)
  intros.
  rewrite Mlet_simpl, <-Hp1d; unfold Mfst; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p1 (Hlift' Hab) _).
  intros.
  rewrite Mlet_simpl, <-Hp2d; unfold Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p2 (Hlift' Hab) _).
 Qed.



 Hypothesis F_notR1_spec: forall a1 b1,
  ~ R1 a1 b1 ->
  F (a1,b1) == prod_distr (F1 a1) (F2 b1). 

 Lemma F_discr_strong: forall  a1b1,
   is_Discrete (F a1b1). 
 Proof.
  intros (a1,b1); destruct (R1_dec a1 b1) as [H | H].
    apply (le_lift_discr_witness _ _ carA2_prop carB2_prop 
      (F1_discr a1) (F2_discr b1) (Hlift' H)).
    eapply is_Discrete_eq_compat; [ apply (Oeq_sym (F_notR1_spec H)) | ].
    apply (is_Discrete_Mlet _ (F1_discr _)).
    intro a2; apply (is_Discrete_Mlet _ (F2_discr _)).
    intro b2; apply is_Discrete_Munit.
 Qed.

 Lemma Fl'_discr_strong: forall (a1b1: A1 * B1), 
   is_Discrete (Fl' a1b1).
 Proof.
  intros; refine (is_Discrete_dl _ _ (F_discr_strong _) (F1_discr _)).
 Qed.

 Lemma Fr'_discr_strong: forall (a1b1: A1 * B1), 
  is_Discrete (Fr' a1b1).
 Proof.
  intros; refine (is_Discrete_dr _ _ (F_discr_strong _) (F2_discr _)).
 Qed.


 Lemma le_dist_F_Fl'_strong: forall (ep'':U),
   (forall a1 b1, ~ R1 a1 b1 -> [1-] (lam' ** mu (F2 b1) (fone _)) <= ep'') ->
   forall ab, le_dist (F ab) (Fl' ab) lam' (max ep' ep'').
 Proof.
  intros ep'' Hep'' (a1,b1).
  destruct (R1_dec a1 b1) as [H | H].
    (* case [R1 a1 b1] *)
    eapply le_dist_weaken_ep; [ apply max_le_right | ].
    refine (le_dist_d_dl _ carA2_prop carB2_prop Hlam' (Fl'_discr_strong _) _ _);
      [ fold (Fl' (a1,b1)) | ].
    refine (d_le_dl _ _ _ carA2_prop carB2_prop (F_discr_strong _) (F1_discr _) _).
    refine (le_p1 (Hlift' H)).
    intro f; rewrite d_expr_sym, <-(le_d (Hlift' H) f (fzero _)), 
      <-max_le_right; trivial.
    (* case [~R1 a1 b1] *)
    eapply le_dist_weaken_ep; [ apply max_le_left | ].
    refine (le_dist_d_dl _ carA2_prop carB2_prop Hlam' (Fl'_discr_strong _) _ _);
      [ fold (Fl' (a1,b1)) | simpl ].
    refine (d_le_dl _ _ _ carA2_prop carB2_prop (F_discr_strong _) (F1_discr _) _).
    rewrite  (F_notR1_spec H), Mfst_prod_distr.
    simpl; intro f; apply (mu_monotonic (F1 a1)); auto.
    rewrite (F_notR1_spec H), Mfst_prod_distr.
    intros f; rewrite <-(Hep'' _ _ H).
    rewrite d_expr_sym; apply (d_expr_distr_mult _ _ _ Hlam').
 Qed.

 Lemma le_dist_F_Fr'_strong: forall (ep'':U),
   (forall a1 b1, ~ R1 a1 b1 -> [1-] (lam' ** mu (F1 a1) (fone _)) <= ep'') ->
   forall (ab:A1*B1), le_dist (F ab) (Fr' ab) lam' (max ep' ep'').
 Proof.
  intros ep'' Hep'' (a1,b1).
  destruct (R1_dec a1 b1) as [H | H].
    (* case [R1 a1 b1] *)
    eapply le_dist_weaken_ep; [ apply max_le_right | ].
    refine (le_dist_d_dr _ carA2_prop carB2_prop Hlam' (Fr'_discr_strong _) _ _);
      [ fold (Fr' (a1,b1)) | simpl ].
    refine (d_le_dr _ _ _ carA2_prop carB2_prop (F_discr_strong _) (F2_discr _) _).
    refine (le_p2 (Hlift' H)).
    intro f; rewrite d_expr_sym, <-(le_d (Hlift' H) (fzero _) f), 
      <-max_le_left; trivial.
    (* case [~R1 a1 b1] *)
    eapply le_dist_weaken_ep; [ apply max_le_left | ].
    refine (le_dist_d_dr _ carA2_prop carB2_prop Hlam' (Fr'_discr_strong _) _ _);
      [ fold (Fr' (a1,b1)) | simpl ].
    refine (d_le_dr _ _ _ carA2_prop carB2_prop (F_discr_strong _) (F2_discr _) _).
    rewrite  (F_notR1_spec H), Msnd_prod_distr.
    simpl; intro f; apply (mu_monotonic (F2 b1)); auto.
    rewrite (F_notR1_spec H), Msnd_prod_distr.
    intros f; rewrite <-(Hep'' _ _ H).
    rewrite d_expr_sym; apply (d_expr_distr_mult _ _ _ Hlam').
 Qed.

 Lemma le_lift_Mlet_discr_strong: forall (ep'':U),
   (forall a1 b1, ~ R1 a1 b1 ->
     max ([1-] (lam' ** mu (F1 a1) (fone _))) ([1-] (lam' ** mu (F2 b1) (fone _))) <= ep'') ->
  le_lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) (lam * lam') (ep + max ep' ep'').
 Proof.
  intros ep'' Hep''.
  destruct Hlift as (Hlam, Hd_dist, Hd_ran, Hp1d, Hp2d).
  assert (Haux_d: is_Discrete (Mlet d (fun a : A1 * B1 => prod_distr (Munit a) (F a)))).
    apply (is_Discrete_Mlet _ d_discr).
    intros ab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intros ab'; apply (is_Discrete_Mlet _ (F_discr_strong _)).
    intros; apply is_Discrete_Munit.
  assert (Haux_dl': is_Discrete (Mlet dl' (fun ab => prod_distr (Munit ab) (Fl' ab)))).
    apply (is_Discrete_Mlet _ dl'_discr).
    intros ab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intro; apply (is_Discrete_Mlet _ (Fl'_discr_strong _)).
    intro; apply is_Discrete_Munit.
  assert (Haux_dr': is_Discrete (Mlet dr' (fun ab => prod_distr (Munit ab) (Fr' ab)))).
    apply (is_Discrete_Mlet _ dr'_discr).
    intros ab; apply (is_Discrete_Mlet _ (is_Discrete_Munit _)).
    intro; apply (is_Discrete_Mlet _ (Fr'_discr_strong _)).
    intro; apply is_Discrete_Munit.
  constructor.
  transitivity (1 * 1)%R; auto with real.
  (* distance *)
  intros f g.
  apply max_le.
    rewrite <-Mfst_dl'_Fl'.
    apply le_dist_Mlet; clear f g.
    refine (le_dist_Mlet_discr F Fl' Hlam Hlam' _ _ carA1B1_prop 
      carA2B2_prop Haux_d Haux_dl' (range_True _) (range_True _) _ _).
      apply (le_dist_d_dl' Hlam).
      intros (a,b) _; apply le_dist_F_Fl'_strong.
      intros a1 b1 H; rewrite <-(Hep'' _ _ H); apply max_le_left.
    rewrite <- Msnd_dr'_Fr'.
    apply le_dist_Mlet; clear f g.
    refine (le_dist_Mlet_discr F Fr' Hlam Hlam' _ _ carA1B1_prop 
      carA2B2_prop Haux_d Haux_dr' (range_True _) (range_True _) _ _).
      apply (le_dist_d_dr' Hlam).
      intros (a,b) _; apply le_dist_F_Fr'_strong.
      intros a1 b1 H; rewrite <-(Hep'' _ _ H); apply max_le_right.
  (* range *)
  apply range_Mlet with (prodP R1).
  exact Hd_ran. 
  intros (a,b) H'. apply (le_r (Hlift' H')).    
  (* projections *)
  intros.
  rewrite Mlet_simpl, <-Hp1d; unfold Mfst; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p1 (Hlift' Hab) _).
  intros.
  rewrite Mlet_simpl, <-Hp2d; unfold Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p2 (Hlift' Hab) _).
 Qed.

 Lemma le_lift_Mlet_discr_lossless: 
   (forall a1 b1,  ~ R1 a1 b1 ->  mu (F1 a1) (fone _) == 1 /\
      mu (F2 b1) (fone _) == 1) ->
   le_lift R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) (lam * lam') (ep + ep').
 Proof.
  intros HF.
  eapply le_lift_weaken with R2 (lam * lam')%R (ep + max ep' 0); trivial.
  rewrite max_eq_right; trivial.
  apply le_lift_Mlet_discr_strong.  
    intros a b H; destruct (HF _ _ H) as (HF1,HF2).
    rewrite HF1, HF2.
    setoid_replace (lam' ** 1) with 1; [ | split; trivial; apply (multRU_ge1 _ Hlam') ].
    apply max_le; apply Uinv_le_perm_left; trivial.
 Qed.

End  DISCR_LIFT.
 
End LE_LIFT.

End Symm_lift.

Add Parametric Morphism A B : (le_lift (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> 
  Oeq (O:=Distr B) ==> (@eq R) ==> Oeq (O:=U) ==> inverse impl
  as elift_morph.
Proof.
 unfold impl, Fimp2; intros R1 R2 H d1 d2 H0 d3 d4 H1 d5 d6 H2 ep lam1 lam2 H3 H4.
 eapply le_lift_weaken. 
 apply H.
 trivial.
 rewrite H3; trivial.
 eapply le_lift_eq_compat with d2 d4 d6 ep lam2; auto.
Qed.



Section Asym_lift.

(* Expression used to define the [lambda-epsilon Distance] *)
Section LE_DIST_EXPR_ASYM.

 Definition d_expr_asym A B (d1:Distr A) (d2:Distr B) (lam:R) f1 f2 :=
  mu d1 f1 - lam ** (mu d2 f2).

 Lemma d_expr_asym_nul : forall A (d:Distr A) (lam:R) f,
  (1 <= lam)%R -> d_expr_asym d d lam f f == 0. 
 Proof.
  unfold d_expr_asym; intros.
  apply Uminus_le_zero; auto.
 Qed.

 Lemma d_expr_asym_trans : forall A B C (d1:Distr A) (d2:Distr B) (d3:Distr C) 
  (lam lam':R) f1 f2 f3,
  (1 <= lam)%R ->
  (1 <= lam')%R ->
  let ep  := d_expr_asym d1 d2 lam f1 f2 in
  let ep' := d_expr_asym d2 d3 lam' f2 f3 in 
  d_expr_asym d1 d3 (lam * lam') f1 f3 <= ep + lam ** ep'.
 Proof.
  unfold d_expr_asym at 3; intros A B C d1 d2 d3 lam lam' 
    f1 f2 f3  Hlam Hlam' ep ep'.
  rewrite Uminus_triang_ineq with (c:= lam ** (mu d2 f2)).
  apply Uplus_le_compat_right.
  rewrite <-(Rmult_multRU_assoc _ Hlam Hlam'),
    (multRU_distr_minus_l _ _ Hlam).
  apply multRU_le_compat; [ | | auto]; fourier.  
 Qed.

 Lemma d_expr_asym_lam_weaken : forall A B (d1: Distr A) (d2: Distr B) 
  (lam lam': R) f1 f2,
  (0 <= lam)%R ->
  (lam <= lam')%R ->
  d_expr_asym d1 d2 lam' f1 f2 <= d_expr_asym d1 d2 lam f1 f2.
 Proof.
  unfold d_expr_asym; intros.
  apply Uminus_le_compat_right, multRU_le_compat; trivial.
 Qed.

 Lemma d_expr_asym_eq_compat : forall A B (d1 d1':Distr A) (d2 d2':Distr B) 
  (lam lam':R) f1 f1' f2 f2',
   d1' == d1 ->
   d2' == d2 ->
   lam' = lam ->
   f1' == f1  ->
   f2' == f2 ->
   d_expr_asym d1' d2' lam' f1' f2' ==  d_expr_asym d1 d2 lam f1 f2. 
 Proof.
  unfold d_expr_asym.
  intros A B d1 d1' d2 d2' lam lam' f1 f1' f2 f2' Hd1 Hd2 Hlam Hf1 Hf2.
  rewrite (mu_stable_eq d1' _ _ Hf1), (mu_stable_eq d2' _ _ Hf2),
    (ford_eq_elim Hd1 f1), (ford_eq_elim Hd2 f2), Hlam.
  trivial.
 Qed.

 Lemma d_expr_asym_mu_compat : forall A (AeqU:A -> A -O-> U) (d:Distr A) (lam:R),
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  forall f1 f2,
  d_expr_asym d d lam f1 f2 <= 
  mu d (fun a => f1 a - lam ** f2 a).
 Proof.
  unfold d_expr_asym; intros A AeqU d lam cover_uR Hd Hlam f1 f2.
  rewrite <-mu_stable_le_minus, (Rmult_mu _ cover_uR Hd Hlam); trivial.
 Qed.

 Lemma d_expr_asym_Mlet_right: forall (A B:Type) (d:Distr A) (F1 F2: A -> Distr B) 
  AeqU lam (ep:U),
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  forall f g,
  (forall a, d_expr_asym (F1 a) (F2 a) lam f g <= ep) ->
  d_expr_asym (Mlet d F1) (Mlet d F2) lam  f g <= ep.
 Proof.
  intros A B d F1 F2 AeqU lam ep Heq Hd Hlam f g H; unfold d_expr_asym.
  rewrite 2 Mlet_simpl, <-(Rmult_mu _ Heq Hd Hlam).
  rewrite mu_stable_le_minus, <-(mu_cte_le d ep).
  apply mu_monotonic; intro a; apply (H a).
 Qed.


End LE_DIST_EXPR_ASYM.



(* [Lambda-Epsilon]-Distance between two distributions *)
Section LE_DIST_ASYM.

 Definition le_dist_asym A (d1 d2:Distr A) (lam:R) (ep:U) :=
  forall f, d_expr_asym d1 d2 lam f f <= ep.

 Lemma le_dist_asym_nul A (d: Distr A) (lam:R):
  (1 <= lam)%R ->
  le_dist_asym d d lam 0.
 Proof.
  unfold le_dist_asym; intros.
  rewrite d_expr_asym_nul; trivial.
 Qed.

 Lemma le_dist_asym_trans A (d1 d2 d3: Distr A) (lam lam':R) (ep ep':U) :
  (1 <= lam)%R ->
  (1 <= lam')%R ->
  le_dist_asym d1 d2 lam ep ->
  le_dist_asym d2 d3 lam' ep' ->
  le_dist_asym d1 d3 (lam * lam') (ep + lam ** ep').
 Proof.
  unfold le_dist_asym; intros A d1 d2 d3 lam lam' ep ep' Hlam Hlam' H12 H23 f.
  rewrite d_expr_asym_trans with (d2:=d2) (f2:=f); trivial.
  apply Uplus_le_compat.
    trivial.
    apply multRU_le_compat; [ | | auto]; fourier.  
 Qed.

 Lemma le_dist_asym_weaken_lam A (d1 d2:Distr A) (lam lam':R) (ep:U) :
  (0 <= lam' <= lam)%R ->
  le_dist_asym d1 d2 lam' ep ->
  le_dist_asym d1 d2 lam ep.
 Proof.
  unfold le_dist_asym; intros A d1 d2 lam lam' ep (?,?) Hf f.
  rewrite <-(Hf f); apply d_expr_asym_lam_weaken; auto.
 Qed.

 Lemma le_dist_asym_weaken_ep A (d1 d2:Distr A) (lam:R) (ep ep':U) :
  ep' <= ep ->
  le_dist_asym d1 d2 lam ep' ->
  le_dist_asym d1 d2 lam ep.
 Proof.
  unfold le_dist_asym; intros.
  transitivity ep'; auto.
 Qed.

 Lemma le_dist_asym_weaken A (d1 d2:Distr A) (lam lam':R) (ep ep':U) :
  ep' <= ep ->
  (0 <= lam' <= lam)%R ->
  le_dist_asym d1 d2 lam' ep' ->
  le_dist_asym d1 d2 lam ep.
 Proof.
  intros.
  apply le_dist_asym_weaken_ep with ep'; trivial.
  apply le_dist_asym_weaken_lam with lam'; trivial.
 Qed.    

 Lemma le_dist_asym_D1_0 : forall A (d1 d2:Distr A),
  le_dist_asym d1 d2 R1 0 -> d1 <= d2.
 Proof.
  unfold le_dist_asym, d_expr_asym; intros A d1 d3 H f.
  apply Uminus_zero_le; split; trivial.
  rewrite <-(H f), multRU_1_l; trivial.
 Qed.

 Lemma le_dist_asym_Mlet : forall A B (d1 d2:Distr A) (F:A->Distr B) (lam:R)     (ep:U),
  le_dist_asym d1 d2 lam ep ->
  le_dist_asym (Mlet d1 F) (Mlet d2 F) lam ep.
 Proof.
  unfold le_dist_asym, d_expr_asym; intros.
  rewrite 2 Mlet_simpl; auto.
 Qed.

 Lemma le_dist_asym_Mlet_right: forall (A B:Type) (d:Distr A) (F1 F2: A -> Distr B) 
   AeqU lam ep,
  (forall a : A, cover (eq a) (AeqU a)) ->
  is_Discrete d ->
  (1 <= lam)%R ->
  (forall a, le_dist_asym (F1 a) (F2 a) lam ep) ->
  le_dist_asym (Mlet d F1) (Mlet d F2) lam ep.
 Proof.
   unfold le_dist_asym; intros A B d F1 F2 AeqU lam ep Heq Hd Hlam H f.
   apply d_expr_asym_Mlet_right with AeqU; auto.
 Qed.

 Lemma le_dist_le_dist_asym: forall (A:Type) (d1 d2: Distr A) lam ep, 
  (1 <= lam)%R ->
  le_dist_asym d1 d2 lam ep ->
  le_dist_asym d2 d1 lam ep ->
  le_dist d1 d2 lam ep.
 Proof.
  unfold le_dist_asym, le_dist.
  intros A d1 d2 lam ep Hlam H1 H2 f.
  apply (d_expr_le_intro _ _ _ _ _ Hlam);
   [ apply H2 | apply H1 ].
 Qed.


Section DIST_DISCR_BOUND.

 Variable A : Type.
 Variable AeqU : A -> A -O-> U.
 Hypothesis cover_uR: forall a : A, cover (eq a) (AeqU a).

 Variable d1 d2 : Distr A.
 Variable lam:R.

 Hypothesis Hlam: (1 <= lam)%R.

 Variable p: nat -> A.
 Hypothesis d1_discr : Discrete (@eq A) p d1.
 Hypothesis d2_discr : Discrete (@eq A) p d2.

 Let P : A -> boolO := 
   fun a => Uleb (lam ** mu d2 (AeqU a)) (mu d1 (AeqU a)).

 Lemma d_expr_asym_restr_le:forall f,
   mu d1 f - lam ** (mu d2 f) <=  mu d1 (restr P f) - lam ** (mu d2 (restr P f)).
 Proof.
  intros.
  rewrite (mu_restr_split d1 P f), (mu_restr_split d2 P f).
  rewrite <-(multRU_distr_plus_l _ _ Hlam).
  rewrite Uplus_minus_perm_assoc, (Uminus_le_zero (mu d1 (restr (negP P) f))),
    Uplus_zero_right; trivial.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <-(multRU_serie _ Hlam).
  apply serie_le_compat; intro.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
    rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
      (coeff_first_repr _ cover_uR d2_discr _ H5).
    unfold restr, negP, negb, P.
    case_eq (Uleb (lam ** (mu d2) (AeqU (p k))) ((mu d1) (AeqU (p k)))); intro Heq.
      rewrite 2 Umult_zero_right; trivial.
      pose proof (Ult_le (Uleb_complete Heq)).
      rewrite <-(Umult_multRU_assoc _ _ Hlam).
      apply Umult_le_compat_left; apply (Ult_le (Uleb_complete Heq)).
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
 Qed.

 Lemma d_expr_asym_restr_fone:forall f,
   mu d1 (restr P f) - lam ** (mu d2 (restr P f)) <=
   mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _))).
 Proof.
  intros.
  rewrite 2 (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    2 (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <- 2 (multRU_serie _ Hlam).
  rewrite serie_minus_le, serie_minus_eq; unfold fminus.
    (* 1st subgoal *)
    apply serie_le_compat; intros k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        rewrite 2 Umult_one_right, <-(Umult_multRU_assoc _ _ Hlam), 
          <-Uminus_distr_left; auto.
        repeat Usimpl; trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
    (* 2nd subgoal *)
    intro k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H;
        try (repeat (Usimpl || multRU_simpl)); trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); Usimpl; multRU_simpl; trivial.
    (* 3rd subgoal *)
    apply wretract_le with (2:=wretract_coeff _ cover_uR p d1);
     intro; auto.
 Qed.

 Lemma d_expr_asym_restr_serie:forall f,
   mu d1 (restr P f) - lam ** (mu d2 (restr P f)) <=
   serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)).
 Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  rewrite <-(multRU_serie _ Hlam).
  rewrite serie_minus_le; unfold fminus.
  apply serie_le_compat; intro k.
  rewrite <-(Umult_multRU_assoc _ _ Hlam), <-Uminus_distr_left; trivial.
 Qed.

 Lemma d_expr_asym_restr_serie_inv:
  serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) <= 
  mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _))).
 Proof.
  intros.
  rewrite (mu_is_Discrete _ cover_uR (mkDiscr d1_discr)),
    (mu_is_Discrete _ cover_uR (mkDiscr d2_discr)); simpl.
  transitivity  (serie (fun k => coeff AeqU p d1 k * restr P (fone A) (p k) - 
    (lam ** ((coeff AeqU p d2 k) * restr P (fone A) (p k))))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        repeat Usimpl; trivial.
        rewrite (Uminus_le_zero _ _ (Ult_le H)); trivial.
      (* not first repr *)
        rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
  rewrite <-(multRU_serie _ Hlam).
  rewrite serie_minus_eq; trivial.
    intros k.
    apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
      (* first repr *)
      rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
        (coeff_first_repr _ cover_uR d2_discr _ H5).
      unfold P, restr, fone.
      generalize (Uleb_spec  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))).
      case (Uleb  (lam ** mu d2 (AeqU (p k))) (mu d1 (AeqU (p k)))); intro H.
        repeat Usimpl; trivial.
        Usimpl; multRU_simpl; trivial.
      (* not first repr *)
      rewrite 2 (coeff_not_first_repr _ _ _ _ H5); Usimpl; multRU_simpl; trivial.
   apply wretract_le with (2:=wretract_coeff _ cover_uR p d1);
     intro; auto.
 Qed.


 (* Characterization of the [lam-eps] distance for discrete distributions *)
 Lemma le_dist_asym_discr_ub: 
   le_dist_asym d1 d2 lam 
   (mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _)))).
 Proof.
  unfold le_dist_asym, d_expr_asym; intros f.
  rewrite d_expr_asym_restr_le, d_expr_asym_restr_fone; trivial.
 Qed.

 Lemma le_dist_asym_discr_lb: forall ep, 
   le_dist_asym d1 d2 lam ep ->
   mu d1 (restr P (fone _)) - lam ** (mu d2 (restr P (fone _))) <= ep.
 Proof.
  unfold le_dist_asym, d_expr_asym; intuition.
 Qed.

 Lemma le_dist_asym_discr_ub_serie: 
   le_dist_asym d1 d2 lam 
   (serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k))). 
 Proof.
  intros f.
  rewrite le_dist_asym_discr_ub.
  apply d_expr_asym_restr_serie.  
 Qed.

 Lemma le_dist_asym_discr_lb_serie: forall ep, 
   le_dist_asym d1 d2 lam ep ->
   serie (fun k => coeff AeqU p d1 k - lam ** (coeff AeqU p d2 k)) <= ep.
 Proof.
  intros ep H.
  rewrite <-(le_dist_asym_discr_lb H).
  apply d_expr_asym_restr_serie_inv.  
 Qed.

 Lemma le_dist_asym_discr_pointwise_ub: forall (F:A -> U),
  (forall (a:A), mu d1 (AeqU a) - lam ** (mu d2 (AeqU a)) <= F a) ->
  le_dist_asym d1 d2 lam (serie (fun k => F (p k))).
 Proof.
  intros F HF.
  eapply le_dist_asym_weaken with (lam':=lam); 
    [ | split; fourier | apply le_dist_asym_discr_ub_serie ].
  apply serie_le_compat; intro k.
  rewrite <-HF.
  apply (cover_elim (cover_not_first_repr _ _ cover_uR p) k); 
    [auto | | ]; intros [H4 H5].
    rewrite (coeff_first_repr _ cover_uR d1_discr _ H5),
      (coeff_first_repr _ cover_uR d2_discr _ H5); trivial.
    rewrite 2 (coeff_not_first_repr _ _ _ _ H5); repeat Usimpl; trivial.
 Qed.


End DIST_DISCR_BOUND.


End LE_DIST_ASYM.


Add Parametric Morphism A B : (@d_expr_asym A B)
 with signature Oeq (O:=Distr A) ==> Oeq (O:=Distr B) ==> 
  (@eq R)  ==> Oeq (O:=MF A) ==> Oeq (O:=MF B) ==> Oeq (O:=U) 
 as d_expr_asym_eq_compat_morph.
Proof.
 intros; apply d_expr_asym_eq_compat; trivial.
Qed.


(* [Lambda-Epsilon]-Lift of a relation to distributions *)
Section LE_LIFT_ASYM.

 Record le_lift_asym A B (S:A -> B -> Prop) (d:Distr (A * B))
  (d1:Distr A) (d2:Distr B) (lam:R) (ep:U) := 
  Build_elift_asym
  {
   le_lam_asym : (1 <= lam)%R;
   le_d_asym   : forall f, mu d1 f - lam ** (mu (Mfst d) f) <= ep;
   le_r_asym   : range (prodP S) d;
   le_p1_asym  :  forall f, mu (Mfst d) f <= mu d1 f;
   le_p2_asym  :  forall g, mu (Msnd d) g <= mu d2 g
  }.

 Lemma le_lift_asym_elim: forall A B (S:A -> B -> Prop) (d1:Distr A) (d2:Distr B) 
  d (lam:R) ep (f:A -o> U) (g:B -o> U),
  (forall a b, S a b -> f a <= g b) ->
  le_lift_asym S d d1 d2 lam ep ->
  d_expr_asym d1 d2 lam f g <= ep.
 Proof.
  intros A B S d1 d2 d lam ep f g Hfg (Hlam, Hdist, Hrange, Hp1, Hp2). 
  unfold d_expr_asym, le_dist_asym.
  rewrite (Uminus_le_compat_right _ (lam ** (mu (Msnd d)) g)). 
    rewrite <-(Hdist f).   
    apply Uminus_le_compat_right, multRU_le_compat; 
      [ fourier | trivial | ].
    unfold Mfst, Msnd; repeat rewrite Mlet_simpl.
    apply range_le with (1:=Hrange); intros; apply (Hfg _ _ H).
    apply multRU_le_compat; [ fourier | | ]; trivial.
 Qed.

 Lemma le_lift_asym_true : forall A B (d1:Distr A) (d2:Distr B) lam,
  (1 <= lam)%R ->
  le_lift_asym (fun _ _ => True) (prod_distr d1 d2) d1 d2 lam
  (([1-] (lam ** (mu d2 (fone _)))) * mu d1 (fone _)).
 Proof.
  intros A B d1 d2 lam Hlam.
  constructor; trivial.
  (* distance *)
  intros f.
  rewrite <-(Umult_one_left (mu d1 f)). 
  rewrite (ford_eq_elim (Mfst_prod_distr d1 d2) f).
  unfold fcte; simpl.
  rewrite (mu_stable_mult d1 (mu d2 (fone _)) f),
    <-(Umult_multRU_assoc _ _ Hlam).
  rewrite <-Uminus_distr_left, Uminus_one_left.
  auto.
  (* range *)
  apply range_True.
  (* projections *)
  intros.
  apply (mu_monotonic d1 (fun x : A => (mu d2) (fun _ : B => f x)) f).
  refine (ford_le_intro _); intro a; apply mu_cte_le.
  intros.
  rewrite (mu_monotonic d1 (fun _ => mu d2 (fun b => g b)) 
    (fcte A (mu d2 g))); [ auto | ].
  unfold fcte; intros _; apply mu_monotonic; auto.
 Qed.

 Lemma le_lift_asym_Munit : forall A (x y:A) (P:relation A) (lam:R) , 
  (1 <= lam)%R ->
  P x y -> 
  le_lift_asym P (Munit (x,y)) (Munit x) (Munit y) lam 0.
 Proof.
  intros; constructor; trivial.
  (* distance *)
  intros.
  unfold Mfst, Msnd; repeat rewrite Mlet_unit, d_expr_asym_nul; auto.
  (* range *)
  apply range_Munit with (1:=H0).
 Qed.

 Lemma le_lift_asym_Mlet : forall (A1 A2 B1 B2: Type) (R1: A1 -> B1 -> Prop)
  (R2:A2 -> B2 -> Prop) (ABeqU: (A1 * B1)  -> (A1 * B1) -O-> U) (d:Distr (A1 * B1)) 
  (d1:Distr A1) (d2:Distr B1) (F:A1 * B1 -> Distr (A2 * B2))
  (F1:A1 -> Distr A2) (F2:B1 -> Distr B2) (lam lam':R) (ep ep':U),
  (forall ab : A1 * B1, cover (eq ab) (ABeqU ab)) ->
  is_Discrete d ->
  (1 <= lam')%R -> 
  le_lift_asym R1 d d1 d2 lam ep ->
  (forall (x:A1) (y:B1), R1 x y -> le_lift_asym R2 (F (x, y)) (F1 x) (F2 y) lam' ep') ->
  le_lift_asym R2 (Mlet d F) (Mlet d1 F1) (Mlet d2 F2) 
  (lam * lam') 
  (ep + lam ** ep').
 Proof.
  intros A1 A2 B1 B2 R1 R2 ABeqU d d1 d2 F F1 F2 lam lam'  ep ep' 
    HeqU Hdiscr Hlam' (Hlam, Hd_dist, Hd_ran, Hp1d, Hp2d) HF.
  constructor.
  transitivity (1 * 1)%R; auto with real.
  (* distance *)
  intros.
  rewrite (Uminus_triang_ineq _ _ (lam ** (mu (Mlet (Mfst d) F1) f))).
  apply Uplus_le_compat.
    apply (Hd_dist (fun x : A1 => (mu (F1 x)) f)).
    rewrite <-(Rmult_multRU_assoc _ Hlam Hlam'),
      (multRU_distr_minus_l _ _ Hlam).
    apply multRU_le_compat; [ fourier | trivial | ].
    unfold Mfst; repeat rewrite Mlet_simpl. 
    rewrite <-(Rmult_mu _ HeqU Hdiscr Hlam'), mu_stable_le_minus.
    rewrite <-(mu_cte_le d ep'); unfold fcte.
    apply (range_le Hd_ran); intros (a,b) Hab; simpl. 
    apply (le_d_asym (HF _ _ Hab) f).  
  (* range *)
  apply range_Mlet with (prodP R1).
  exact Hd_ran. 
  intros (a,b) H'; apply (le_r_asym (HF _ _ H')).    
  (* projections *)
  intros.
  rewrite Mlet_simpl, <-Hp1d; unfold Mfst; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p1_asym (HF a1 b1 Hab) _).
  intros.
  rewrite Mlet_simpl, <-Hp2d; unfold Msnd; repeat rewrite Mlet_simpl.
  apply range_le with (1:=Hd_ran); intros (a1,b1) Hab; simpl.
  refine (le_p2_asym (HF a1 b1 Hab) _).
 Qed.

 Lemma le_lift_asym_discr_witness: forall A B  (carB : B -> MF B) (carA : A -> MF A) 
   (d:Distr (A * B)) (d1:Distr A) (d2:Distr B) R lam ep,
  (forall a, cover (fun x => a = x) (carA a)) ->
  (forall b, cover (fun x => b = x) (carB b)) ->
  is_Discrete d1 ->
  is_Discrete d2 ->
  le_lift_asym R d d1 d2 lam ep ->
  is_Discrete d.
 Proof.
  intros A B carA carB d d1 d2 R lam ep HcarA HcarB Hd1 Hd2 Hd.
  apply (discr_projs _ _ HcarB HcarA).
    apply discr_ext with (2:=Hd1).
    intros; apply Ule_zero_eq; rewrite (le_p1_asym Hd f); auto.
    apply discr_ext with (2:=Hd2).
    intros; apply Ule_zero_eq; rewrite (le_p2_asym Hd f); auto.
 Qed.

 Lemma le_lift_asym_lift : forall A B (R:A -> B -> Prop) (d1:Distr A) (d2:Distr B) d,
  le_lift_asym R d d1 d2 R1 0 /\ le_lift_asym (fun b a => R a b) (Mswap d) d2 d1 R1 0 <-> 
  lift R d d1 d2.
 Proof.
  split.
  (* ==> *)
  intros ((Hlam, Hdist, Hran, Hp1, Hp2),(Hlam', Hdist', Hran', Hp1', Hp2')).
  constructor.
  (* 1st proj *)
  intro f; split.
    apply (Hp2' f).
    rewrite <-(multRU_1_l (mu d _)).
    apply Uminus_zero_le; split; trivial.
    apply Hdist.
  (* 2nd proj *)
  intro f; split.
    apply (Hp2 f).
    rewrite <-(multRU_1_l (mu d _)).
    apply Uminus_zero_le; split; trivial.
    apply Hdist'.
  (* range *)
  trivial.
  (* <== *)
  intros (Hfst, Hsnd, Hran); split.
  (* left lift *)
  constructor; trivial.
    intro f; rewrite multRU_1_l, <-(Hfst f); auto.
    intro f; rewrite <-(Hfst f); auto.
    intro g; rewrite <-(Hsnd g); auto.
  (* right lift *)
  constructor; trivial.
    intro g; rewrite multRU_1_l, (ford_eq_elim (Mswap_fst d)), <-(Hsnd g); auto.
    intros f Hf; apply (Hran (fun ab => f (snd ab,fst ab))); auto.
    intro g; rewrite  (ford_eq_elim (Mswap_fst d)), <-(Hsnd g); auto.
    intro f; rewrite  (ford_eq_elim (Mswap_snd d)), <-(Hfst f); auto.
 Qed.

 Lemma le_lift_asym_weaken: forall A B d d1 d2 (P P':A -> B -> Prop) 
  (lam lam':R) (ep ep':U), 
  (forall x y, P' x y -> P x y) ->
  (lam' <= lam)%R ->
  ep' <= ep ->
  le_lift_asym P' d d1 d2 lam' ep' -> 
  le_lift_asym P  d d1 d2 lam ep.
 Proof.
  intros A B d d1 d2 P P' lam lam' ep' ep HP Hlam Hep (Hlam', Hdist, Hran).
  constructor; trivial.
  fourier.
  (* distance *)
  intro f.
  rewrite <-Hep, <-(Hdist f).
  apply d_expr_asym_lam_weaken; trivial; fourier.   
  (* range *)
  apply range_weaken with (2:=Hran). 
  unfold prodP; auto.
 Qed.
  
 Lemma le_lift_asym_eq_compat : forall A B (S:A -> B -> Prop) 
  (d d':Distr (A * B)) (d1 d1':Distr A) (d2 d2':Distr B) (lam lam':R) (ep ep':U),
  d == d' -> 
  d1 == d1' -> 
  d2 == d2' -> 
  lam = lam' ->
  ep == ep' ->
  le_lift_asym S d d1 d2 lam ep -> le_lift_asym S d' d1' d2' lam' ep'.
 Proof.
  intros A B R d d' d1 d1' d2 d2' 
   lam lam' ep ep' Heq Heq1 Heq2 Heq3 Heq4 (Hlam, Hdist, Hran, Hp1, Hp2).
  constructor.
  fourier.
  intros; unfold Mfst.
  rewrite <-(ford_eq_elim (@Mlet_eq_compat _ _  d d' 
    (fun ab => Munit (fst ab)) 
    (fun ab => Munit (fst ab)) Heq (Oeq_refl _))).
  rewrite <-(ford_eq_elim Heq1), <-Heq3, <-Heq4.
  apply Hdist.
  apply range_stable_eq with (1:=Heq); trivial.
  intro f; rewrite <-(eq_distr_elim Heq1), <-Hp1.
  apply eq_distr_elim; rewrite Heq; trivial.
  intro f; rewrite <-(eq_distr_elim Heq2), <-Hp2.
  apply eq_distr_elim; rewrite Heq; trivial.
 Qed.

(*
 (* This rule breaks dowm *)
 Lemma le_lift_asym_transp : forall A B (d:Distr (A * B)) (d1:Distr A) 
   (d2:Distr B) R lam ep, 
  le_lift_asym (fun b a => R a b) 
  (Mlet d (fun ab => Munit (snd ab, fst ab))) d2 d1 lam ep ->
  le_lift_asym R d d1 d2 lam ep. 
 Proof.
  intros A B d d1 d2 R lam ep (Hlam, Hdist, Hran, Hp1, Hp2).
  constructor; trivial.
  (* distance *)
  intro f.
  rewrite <-(Hdist g); auto.
  rewrite <-(Hdist g f), <-max_le_right; auto.
  
  (* range *)
  intros f Hf.
  rewrite (Hran (fun ba => f (snd ba,fst ba))).
  rewrite Mlet_simpl; simpl.
  apply (mu_stable_eq d); refine (ford_eq_intro _); intros (a,b); trivial.
  auto.
 Qed.
*)

 Lemma le_lift_asym_prod : forall A B (d:Distr (A * B)) (P:A -> B -> Prop),
  range (prodP P) d ->
  le_lift_asym P d (Mfst d) (Msnd d) R1 0.
 Proof. 
  intros; constructor; trivial.
  intros; repeat rewrite d_expr_asym_nul; auto with real.
 Qed.

 Lemma le_lift_asym_distr0: forall (A B:Type) P lam ep,
   (1 <= lam)%R ->
   le_lift_asym P (distr0 (A*B)) (distr0 A) (distr0 B) lam ep. 
 Proof.
  intros.
  constructor.
    trivial.
    intros; unfold Mfst.
    rewrite (ford_eq_elim (@Mlet_distr0_abs _ _ _)); auto.
    intros f _; trivial.
    intros; unfold Mfst; rewrite Mlet_simpl; trivial.
    intros; unfold Msnd; rewrite Mlet_simpl; trivial.
 Qed.


 (* Sufficient condition to relate two distibutions wrt 
    the equalitiy relation *)
 Section LE_DIST_2_LE_LIFT_ASYM.

  Variable A : Type.

  Variable AeqU : A -> A -O-> U.
  Hypothesis cover_uR : forall a : A, cover (eq a) (AeqU a).

  Variable d1 d2 : Distr A.
  Hypothesis H_d1 : is_Discrete d1.
  Hypothesis H_d2 : is_Discrete d2.

  Let p := parity_split (D_points H_d1) (D_points H_d2).
  Let dd := Mlet (dmin _ cover_uR p d1 d2) (fun a => Munit (a,a)).
 
  Lemma le_lift_asym_eq_intro: forall lam ep,
   (1 <= lam)%R ->
   le_dist_asym d1 d2 lam ep ->
   le_lift_asym (@eq A) dd d1 d2 lam ep.
  Proof.
   intros.
   constructor; trivial.
   (* distance *)
   set (P:=fun a : A => Uleb (mu d1 (AeqU a)) (mu d2 (AeqU a))).
   intros f.
   change (mu d1 f - lam ** (mu (dmin AeqU cover_uR p d1 d2) f) <= ep).
   rewrite (mu_restr_split d1 P).
   eapply Ole_trans with (_ - lam ** _).
   apply Uminus_le_compat_right.
   apply multRU_le_compat.
   fourier.
   trivial.
   apply Oeq_le; symmetry.
   apply (dmin_simpl _ cover_uR (disc_eqpoint_l H_d1 H_d2)
     (disc_eqpoint_r H_d1 H_d2) _ Uleb_correct_conv  Uleb_complete_conv f).
   rewrite <-multRU_distr_plus_l, Uplus_minus_perm_assoc; trivial.
   match goal with |- ?X1 + _ <= _ => 
     setoid_replace X1 with (@D0 U) by auto
   end.
   Usimpl; apply H0.
   (* range *)
   eapply range_Mlet with (1:=range_True _).
   intros a _; apply (range_Munit _ _ _ (eq_refl a)).
   (* projections *)
   intro; unfold dd, Mfst.
   rewrite 2 Mlet_simpl.
   apply (@dmin_le_d1 _ _ cover_uR p d1 d2 (disc_eqpoint_l H_d1 H_d2) f).
   intro; unfold dd, Msnd.
   rewrite 2 Mlet_simpl.
   apply (@dmin_le_d2 _ _ cover_uR p d1 d2 (disc_eqpoint_r H_d1 H_d2) g).
  Qed.

 End LE_DIST_2_LE_LIFT_ASYM.


(* Transitivity of the lift *)
Section ASYM_LIFT_TRANS.
 
 Variables A B C : Type.
 Variable carA : A -> MF A.
 Variable carB : B -> MF B.
 Variable carC : C -> MF C.

 Hypothesis carA_prop : forall b, cover (fun x => b = x) (carA b).
 Hypothesis carB_prop : forall b, cover (fun x => b = x) (carB b).
 Hypothesis carC_prop : forall b, cover (fun x => b = x) (carC b).

 Variable P : A -> B -> Prop.
 Variable Q : B -> C -> Prop.
 Variable S : A -> C -> Prop.

 Hypothesis P_Q_S : forall x y z, P x y -> Q y z -> S x z.

 Variable d  : Distr (A*B).
 Variable d' : Distr (B*C). 
 Variable ep ep' : U.
 Variable lam lam': R.

 Variable d1 : Distr A.
 Variable d2 : Distr B.
 Variable d3 : Distr C.

 Hypothesis  Hd : le_lift_asym  P d  d1 d2 lam ep.
 Hypothesis  Hd': le_lift_asym Q d' d2 d3 lam' ep'.

 Hypothesis Hd1_discr: is_Discrete d1.
 Hypothesis Hd2_discr: is_Discrete d2.
 Hypothesis Hd3_discr: is_Discrete d3.


 Lemma Hd_discr_asym: 
   is_Discrete d.
 Proof.
  apply (discr_projs _ _ carB_prop carA_prop).
    refine (discr_ext _ _ Hd1_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p1_asym Hd), H; trivial.
    refine (discr_ext _ _ Hd2_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p2_asym Hd), H; trivial.
 Qed.

 Lemma Hd'_discr_asym: is_Discrete d'.
 Proof.
  apply (discr_projs _ _ carC_prop carB_prop).
    refine (discr_ext _ _ Hd2_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p1_asym Hd'), H; trivial.
    refine (discr_ext _ _ Hd3_discr).
    intros f H; apply Ule_zero_eq; rewrite (le_p2_asym Hd'), H; trivial.
 Qed.


 Let carAB: A*B -> MF (A*B) := carProd carA carB.
 Let carBC: B*C -> MF (B*C) := carProd carB carC.
 Let carAB_prop: forall ab, cover (fun x => ab = x) (carAB ab).
 Proof.
  apply (carProd_prop _ _ carA_prop carB_prop).
 Qed.
 Let carBC_prop: forall bc, cover (fun x => bc = x) (carBC bc). 
 Proof.
  apply (carProd_prop _ _ carB_prop carC_prop).
 Qed.

 Definition dfst_asym (b : B) : Distr (B*C) := distr_mult (fun q => carB b (fst q)) d'.
 Definition dsnd_asym (b : B) : Distr (A*B) := distr_mult (fun q => carB b (snd q)) d.

 Let dsnd_asym_le : forall b, 
  mu (dsnd_asym b) (fone _) <= mu d2 (fun b' => carB b b').
 Proof.
  intro; rewrite <-(le_p2_asym Hd); simpl;
    apply (mu_monotonic d); intro; auto.
 Qed. 

 Let dfst_asym_le : forall b, 
  mu (dfst_asym b) (fone _) <=  mu d2 (fun b' => carB b b').
 Proof.
  intro; rewrite <-(le_p1_asym Hd'); simpl;
    apply (mu_monotonic d'); intro; auto.
  Qed.

 Let d_restr : B -> Distr (A*B) := 
  fun b => distr_div (mu d2 (fun b' => carB b b')) (dsnd_asym b) (dsnd_asym_le b) .

 Let d'_restr : B -> Distr (B*C) := 
  fun b => distr_div  (mu d2 (fun b' => carB b b')) (dfst_asym b) (dfst_asym_le b).


 Definition dd'_asym : Distr (A * C) := 
  Mlet d2 (fun b => 
   Mlet (d_restr b) (fun p => 
    Mlet (d'_restr b) (fun q => Munit (fst p, snd q)))).


 Lemma dd'_asym_comm: dd'_asym ==
   Mlet d2 (fun b => 
     Mlet (d'_restr b) (fun q => 
       Mlet (d_restr b) (fun p => Munit (fst p, snd q)))).
 Proof.
  apply eq_distr_intro; intro f.
  unfold dd'_asym; rewrite 2 Mlet_simpl; simpl.
  apply (mu_stable_eq d2); refine (ford_eq_intro _); intro b.
  apply Udiv_eq_compat; [ | auto ].
  transitivity (mu d (fdiv (mu d2 (fun b' => carB b b')) 
    (fun ab => mu d' (fun bc => carB b (snd ab) * 
      (carB b (fst bc) * f (fst ab, snd bc)))))). 
    unfold fdiv; apply (mu_stable_eq d); refine (ford_eq_intro _); intro ab.
    rewrite <-Umult_div_assoc, <-(mu_stable_mult d' 
      (carB b (snd ab))); trivial.
    rewrite <-(le_p1_asym Hd'); simpl; apply (mu_monotonic d'); 
      intro bc; auto.
  transitivity (mu d' (fdiv (mu d2 (fun b' => carB b b')) 
    (fun bc => mu d (fun ab =>  carB b (fst bc) * 
      (carB b (snd ab) * f (fst ab, snd bc)))))).
    Focus 2.
    unfold fdiv; apply (mu_stable_eq d'); refine (ford_eq_intro _); intro bc.
    rewrite <-Umult_div_assoc, <-(mu_stable_mult d 
      (carB b (fst bc))); trivial.
    rewrite <-(le_p2_asym Hd); simpl; apply (mu_monotonic d); 
      intro ab; auto.
    unfold fdiv; rewrite 2 mu_stable_div_strong.
      apply Udiv_eq_compat_left.
      rewrite (@Discr_distr_comm_elim _ _ _ d d' carAB_prop Hd_discr_asym).
      apply mu_stable_eq; refine (ford_eq_intro _); intro bc.
      apply mu_stable_eq; refine (ford_eq_intro _); trivial.
      unfold fcte; intros bc. 
      rewrite <-(le_p2_asym Hd); simpl.
      apply (mu_monotonic d); intro ab; rewrite Umult_sym, <-Umult_assoc; auto.
      unfold fcte; intros ab.
      rewrite <-(le_p1_asym Hd'); simpl.
      apply (mu_monotonic d'); intro bc; rewrite Umult_sym, <-Umult_assoc; auto. 
 Qed.


 Lemma Mfst_dd'_asym_le_Mfst_d: Mfst dd'_asym <= Mfst d.
 Proof.
  refine (ford_le_intro _); intro f.
  unfold Mfst, dd'_asym; repeat rewrite Mlet_simpl; simpl.
  rewrite <-(distr_pointwise_sum_r _ carB_prop Hd2_discr d (le_p2_asym Hd)).
  apply (mu_monotonic d2); intro b.
  apply Udiv_le_compat; [ | apply (mu_stable_eq d2);
    refine (ford_eq_intro _); trivial ].
  apply (mu_monotonic d); intro ab.
  rewrite (mu_stable_mult_right d' (f (fst ab))). 
  rewrite (Umult_sym _ (f _)), (Umult_div_assoc _ _ _ 
    (le_p1_asym Hd' (fun b' : B => carB b b'))), Umult_assoc; auto.
 Qed.


 Lemma Msnd_dd'_asym_le_Msnd_d': Msnd dd'_asym <= Msnd d'.
 Proof.
  refine (ford_le_intro _); intro f.
  unfold Msnd; rewrite 2 Mlet_simpl.  
  rewrite <-(distr_pointwise_sum_l _ carB_prop Hd2_discr d' (le_p1_asym Hd')). 
  rewrite (eq_distr_elim dd'_asym_comm); simpl.
  apply (mu_monotonic d2); intro b.
  apply Udiv_le_compat; [ | apply (mu_stable_eq d2);
    refine (ford_eq_intro _); trivial ].
  apply (mu_monotonic d'); intro bc.
  rewrite (mu_stable_mult_right d (f (snd bc))). 
  rewrite (Umult_sym _ (f _)), (Umult_div_assoc _ _ _ 
    (le_p2_asym Hd (fun b' : B => carB b b'))), Umult_assoc; auto.
 Qed.


 Lemma dd'_asym_range : range (prodP S) dd'_asym.
 Proof.
  intros h Hf; unfold dd'_asym; simpl.
  rewrite <-(mu_zero d2).
  apply (mu_stable_eq d2); simpl; apply ford_eq_intro; intro x; unfold fzero.
  apply (Ueq_orc 0  (mu d2 (fun b' => carB x b'))); [ auto | | ]; intros.
    (*   *)
    apply Oeq_sym; apply Udiv_by_zero; auto.
    (*   *)
    apply Oeq_sym; apply Udiv_zero_eq; auto.
    apply (le_r_asym Hd); intros.
    apply (cover_elim (carB_prop x) (snd x0)); auto; intros [H4 H5]; rewrite H5; Usimpl.
      (*  *)
      trivial.
      (*  *)
      symmetry; apply Udiv_zero_eq.
      apply (le_r_asym Hd'); intros.
      destruct x1; destruct x0; simpl.
      simpl in H4; subst x.
      apply (cover_elim (carB_prop b0) b); auto; intros [H6 H7].
        rewrite H7; auto.
        rewrite H7; Usimpl; subst b0.
        apply Hf; apply P_Q_S with b; trivial.
  Qed.


 Lemma dist_l_aux_asym: le_dist_asym (Mfst d) (Mfst dd'_asym) lam' ep'.
 Proof.
  pose proof (le_lam_asym Hd') as Hlam'.
  assert (Hr: is_Discrete (Mfst d)) by 
    apply (is_Discrete_Mlet _ Hd_discr_asym (fun ab => (is_Discrete_Munit (fst ab)))).
  destruct Hd_discr_asym as (p,Hp); simpl.
  set (p2:=fun k' : nat => snd (p k')).
  (* Use lemma [le_dist_asym_discr_ub_le] to bound the distance *)
  eapply le_dist_asym_weaken with (lam':= lam'); [ | split; fourier | 
    apply (@le_dist_asym_discr_ub _ _ carA_prop _ _ _  Hlam' _ 
    (D_Discr Hr) (enum_le (D_Discr Hr) (Mfst_dd'_asym_le_Mfst_d))) ]. 
  set (P':= restr (fun a => Uleb (lam' ** mu (Mfst dd'_asym) (carA a)) 
    (mu (Mfst d) (carA a))) (fone A)).
  (* Simplify distribution [Mfst dd'_asym] *)
  rewrite Uminus_le_compat_right with (y:= lam' ** 
     mu d (fun ab => mu d' (fun bc => carB (snd ab) (fst bc) * P' (fst ab)) /
        mu d2 (fun b' : B => carB (snd ab) b'))).
    Focus 2.  
    apply multRU_le_compat; [ fourier | apply Rle_refl | simpl ].
    rewrite <-(distr_pointwise_sum_r _ carB_prop Hd2_discr d (le_p2_asym Hd)).
    simpl; apply (mu_monotonic d2); intro b.
    apply Udiv_le_compat.
      apply (mu_monotonic d); intros (a',b'); simpl.
      apply (cover_elim (carB_prop b) b'); [ auto | | ]; intros [H4 H5]; 
        rewrite H5; repeat Usimpl; [ | rewrite H4 ]; trivial.
      apply (mu_stable_eq d2); refine (ford_eq_intro _); intro; trivial.
  (* Discretize the distributions *)
  simpl; rewrite 2 (mu_is_Discrete _ carAB_prop (mkDiscr Hp)); simpl.
  rewrite (discr_distr_simpl _ carAB_prop Hp (fun ab => P' (fst ab))),
   (discr_distr_simpl _ carAB_prop Hp (fun ab => mu d' 
     (fun bc : B * C => carB (snd ab) (fst bc) * P' (fst ab)) /
      mu d2 (fun b'=> carB (snd ab) b'))).
  rewrite <-(multRU_serie _ Hlam'), serie_minus_le; unfold fminus.
  (* Extract as a common factor the term [ [1-] not_first_repr carAB p k * 
     (mu d (carAB (p k)) / mu d2 (fun b' => carB (snd (p k)) b')) ]
     and bound factor [P' (fst (p k))] by [1] *)
  transitivity  (serie (fun k => 
    [1-] not_first_repr carAB p k * mu d (carAB (p k)) * P' (fst (p k)) -
    lam' ** ([1-] not_first_repr carAB p k * 
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b')) *
      mu d' (fun bc => carB (p2 k) (fst bc))))).
    apply serie_le_compat; intro k.
    rewrite Umult_assoc; apply Uminus_le_compat_right.
    apply multRU_le_compat; [ fourier | apply Rle_refl | ]. 
    rewrite <-Umult_assoc; Usimpl.
    rewrite <-Umult_div_assoc, (Umult_sym (mu d _) (mu d' _)),
     (mu_stable_mult_right d'), <-Umult_assoc, (Umult_div_assoc _ (_ * _));
       [ | rewrite <-(le_p2_asym Hd (fun b' : B => carB (snd (p k)) b')),
       Ule_mult_left; unfold carAB, carProd; simpl; auto | rewrite <-(le_p1_asym Hd' 
         (fun b' : B => carB (snd (p k)) b')); simpl; auto ].
    unfold p2; rewrite Umult_sym; Usimpl; auto.
  transitivity (serie (fun k =>
    [1-] not_first_repr carAB p k * mu d2 (fun b' => carB (p2 k) b') *
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b')) -
    lam' ** ([1-] not_first_repr carAB p k * mu (Mfst d') (fun b => carB (p2 k) b) *
    ((mu d (carAB (p k)) * P' (fst (p k))) / mu d2 (fun b' => carB (p2 k) b'))))).  
    apply serie_le_compat; intro k.
    apply Uminus_le_compat.
      rewrite <- 2 Umult_assoc; Usimpl.
      apply (Ueq_orc 0 (mu d2 (fun b' => carB (p2 k) b'))); [ auto | | ]; intro H.
        transitivity (@D0 U); [rewrite H | trivial ].
        rewrite <-(le_p2_asym Hd (fun b' : B => carB (p2 k) b')),
          Ule_mult_right; unfold carAB, carProd; simpl; auto.
        rewrite <-(Umult_sym (_ / _)), (Udiv_mult _ H); trivial.
     rewrite <-(le_p2_asym Hd (fun b' : B => carB (p2 k) b')),
       Ule_mult_right; unfold carAB, carProd; simpl; auto.
     rewrite <- 2 Umult_assoc, (Umult_sym (mu (Mfst _) _)); trivial.
  set (F := fun b => mu d2 (fun b' => carB b b') -
        lam' ** (mu (Mfst d')) (fun b' => carB b b')).
  set (H:= fun ab => mu d (carAB ab) / mu d2 (fun b' => carB (snd ab) b') * 
    F (snd ab)).
  transitivity (serie (fun k => ([1-] not_first_repr carAB p k * H (p k)))).
    apply serie_le_compat; intro k; unfold H, F.
    apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
      [auto | | ]; intros [_ H5].
    rewrite H5; repeat Usimpl.
    rewrite <-(Umult_multRU_assoc _ _ Hlam'), <-Uminus_distr_left,
     <-(Umult_sym (_ - _)); unfold p2; Usimpl; auto.
    rewrite H5 at 1; repeat Usimpl; trivial.
  (* rewrite the serie as two nested series, one summing over the 
     [a]'s and the other summing over the [b]'s *)
  unfold carAB; rewrite (sigma_prod_split_l _ _ p carA_prop carB_prop).
  (* Push factor [F (p2 kb)] outside the inner serie *)
  transitivity (serie (fun kb => [1-] not_first_repr carB p2 kb *
     F (p2 kb) * serie (fun ka => [1-] not_first_repr carAB p ka *
         carB (p2 ka) (p2 kb) * 
         (mu d (carAB (fst (p ka), p2 kb)) / mu d2 (fun b' => carB (p2 kb) b'))))).
    apply serie_le_compat; intro kb; unfold H.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop 
      (fun k => snd (p k))) kb); [auto | intros _ | intros [_ H5]  ].
      2:rewrite H5; repeat Usimpl; trivial.
      rewrite <-Umult_assoc, <-serie_mult with (c:=F (p2 kb)).
      unfold p2; Usimpl; apply serie_le_compat; intro ka.
      rewrite Umult_assoc, Umult_sym; trivial.
    apply (Ule_orc 1 (mu d2 (fun b' => carB (p2 kb) b'))); 
      [ apply class_wretract | | ]; intro Heq.
    (* case [d2 (p2 kb) == 1] *)
    apply wretract_le with (fun k => [1-] not_first_repr carAB p k * mu d (carAB (p k))).
      intro k; rewrite (Uge_one_eq _ Heq), Udiv_one_strong.
      apply (cover_elim (carB_prop (p2 k)) (p2 kb)); [ auto | | ]; intros (H',H'').
        rewrite H''; repeat Usimpl; trivial.
        rewrite <-H', <-surjective_pairing; auto.
    apply wretract_le with (coeff carAB p d).
      intro k; apply (cover_elim (cover_not_first_repr _ _ carAB_prop p) k); 
        [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl.
        rewrite (coeff_first_repr _ carAB_prop Hp _ H5); trivial.
        trivial.
    apply (wretract_coeff _ carAB_prop p d).
    (* case [d2 (p2 kb) < 1] *)
    apply wretract_le with (fun ka  => ([1-] not_first_repr carAB p ka * 
      carB (p2 ka) (p2 kb) * mu d (carAB (fst (p ka), p2 kb))) /
       mu d2 (fun b' => carB (p2 kb) b')).
      intros k.
      apply Oeq_le; symmetry; apply Umult_div_assoc.
      rewrite <-(le_p2_asym Hd (fun b' => carB (p2 kb) b'));
        simpl; unfold carAB, carProd; auto.
    apply (wretract_Udiv _ Heq).
    intro n.
    rewrite le_lub.
    transitivity (serie (fun k => [1-] not_first_repr carAB p k *
      ((mu d) (carAB (p k)) * carB (p2 kb) (p2 k)))).
      apply lub_le_compat; refine (ford_le_intro _); intro; apply sigma_le_compat; intros.
      apply (cover_elim (carB_prop (p2 k)) (p2 kb)); [ auto | | ]; intros (H',H'').
        rewrite H''; repeat Usimpl; trivial.
        rewrite <-H', <-surjective_pairing, <-Umult_assoc; auto.
    rewrite <-(le_p2_asym Hd (fun b' => carB (p2 kb) b')); simpl.
    rewrite (mu_is_Discrete _ carAB_prop (mkDiscr Hp)); simpl.
    rewrite (discr_distr_simpl _ carAB_prop Hp) with (f:=fun ab =>
      carB (p2 kb) (snd ab)); trivial.
  (* Bound the inner serie by [1] *)
  rewrite serie_prod_maj.
  (* Split the serie in two *)
  set (PR:= fun b => B2U (Uleb (lam' ** mu (Mfst d') (fun b' => carB b b')) 
    (mu d2 (fun b' => carB b b')))).
  transitivity (serie (fun k => 
       [1-] not_first_repr carB p2 k * PR (p2 k) * 
       mu d2 (fun b' => carB (p2 k) b') -
       lam' ** ([1-] not_first_repr carB p2 k * PR (p2 k) * 
         mu (Mfst d') (fun b' => carB (p2 k) b')))).
    apply serie_le_compat; intro k.
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat Usimpl; trivial.
      unfold PR, B2U, F.
      match goal with |- context [Uleb ?X1 ?X2] => 
        generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; repeat Usimpl;
          [ trivial | apply (Uminus_le_zero _ _ (Ult_le  Heq)) ]
      end.
  rewrite <-serie_minus_eq.
    Focus 2.
    intros k. 
    apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
      [auto | | ]; intros [_ H5]; rewrite H5; repeat (Usimpl || multRU_simpl); trivial.
    unfold PR, B2U, F.
    match goal with |- context [Uleb ?X1 ?X2] => 
      generalize (Uleb_spec X1 X2); case (Uleb X1 X2); intros Heq; 
        repeat (Usimpl || multRU_simpl); trivial
    end.
    Focus 2.
    apply wretract_le with (fun k => [1-] not_first_repr carB p2 k *
      mu d2 (fun b' => carB (p2 k) b')); [ auto | ].
    intro n.
    rewrite <-(mu_stable_mult d2 ([1-] _)).
    transitivity ([1-] (sigma (fun k => mu d2
      (fmult ( [1-] not_first_repr carB p2 k) (fun b' => carB (p2 k) b'))) n));
      [ | Usimpl; apply sigma_le_compat; intros k _; apply (mu_stable_mult d2) ].
    rewrite <-mu_sigma_eq.
      (* 1st subg *)
      apply mu_fplusok.
      unfold fplusok, fmult, finv, sigma_fun; intro b; fold (p2 n).
      apply (cover_elim (carB_prop (p2 n)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) n); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'; fold (p2 k').
        apply (cover_elim (carB_prop (p2 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
      (* 2nd subg *) 
      intros b k Hk; unfold fmult; fold (p2 k).
      apply (cover_elim (carB_prop (p2 k)) b); [ auto | | ]; intros [H4 H5].
        rewrite H5; Usimpl; trivial.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
            [auto | | ]; intros [H4' H5']; rewrite H5'; repeat Usimpl; trivial.
        rewrite sigma_zero; [ Usimpl; trivial | ].
        intros k' Hk'; fold (p2 k').
        apply (cover_elim (carB_prop (p2 k')) b); [ auto | | ]; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  (* Push the factors multiplying the distributions inside the measured functions and
     the [lam'] term outside the rightmost serie *)
  transitivity (serie (fun k => mu d2 (fmult ([1-] not_first_repr carB p2 k * PR (p2 k))
    (fun b => carB (p2 k) b))) -
            lam' ** serie (fun k => mu (Mfst d') (fmult ([1-] not_first_repr carB p2 k * PR (p2 k))
    (fun b => carB (p2 k) b)))).
    apply Uminus_le_compat; [ | rewrite (multRU_serie _ Hlam'); 
      apply multRU_le_compat; [ fourier | apply Rle_refl | ] ];
        apply serie_le_compat; intro k; apply  mu_stable_mult.
  (* Push the series inside the function being measured by [d2] and [Mfst d'] *)
  assert (Haux: forall b, wretract (fun k => fmult ([1-] not_first_repr carB p2 k * PR (p2 k)) 
    (fun b' => carB (p2 k) b') b)).
      intro b. 
      apply wretract_le with  (fun k => carB (p2 k) b * [1-] not_first_repr carB p2 k);
        [ unfold fmult; intro k; rewrite Umult_sym, Umult_assoc; trivial | ].
      intro k.
      apply (cover_elim (carB_prop (p2 k)) b); auto; intros [H4 H5]; rewrite H5; Usimpl; trivial.
        apply Uinv_le_compat.
        apply (cover_elim (cover_not_first_repr _ _ carB_prop p2) k); 
          [auto | | ]; intros [H4' H5']; rewrite H5'; trivial.
        apply sigma_zero; intros k' Hk'.
        apply (cover_elim (carB_prop (p2 k')) b); auto; intros [H4'' H5''].
          rewrite H5''; auto.
          elim H4'; apply exc_intro with k'; split; [ | rewrite H4, H4'']; trivial.
  rewrite <-2 (mu_serie_eq _ _ Haux).
  (* Use the hypothesis about the distance between [d2] and [Mfst d'] 
     to conclude *)
  apply (le_d_asym Hd').
 Qed.


 Lemma dd'_asym_distance: forall (f : A -O-> U),
  d_expr_asym d1 (Mfst dd'_asym) (lam' * lam)%R f f <= ep + lam ** ep'.
 Proof.
  intro f.
  rewrite Rmult_comm.
  rewrite (@d_expr_asym_trans _ _ _  d1 (Mfst d) (Mfst dd'_asym) lam lam' f f f 
    (le_lam_asym Hd) (le_lam_asym Hd')).
  apply Uplus_le_compat.
    apply (le_d_asym Hd).
    refine (multRU_le_compat _ _ _ (Rle_refl _) _); 
      [ pose proof (le_lam_asym Hd); fourier | ].
    apply (dist_l_aux_asym f).
 Qed.


 Lemma le_lift_asym_trans_discr: le_lift_asym S dd'_asym d1 d3 (lam * lam') 
    (ep + lam ** ep').
 Proof.
  constructor.
    (* [1 <= lam] *) 
    rewrite <-(Rmult_1_r 1).
    apply Rmult_le_compat; auto with real;
     [ apply (le_lam_asym Hd) | apply (le_lam_asym Hd') ].
    (* distance *)
    intros; rewrite Rmult_comm; apply dd'_asym_distance.
    (* range *)
    apply dd'_asym_range.
    (* projections *)
    intro f; rewrite (Mfst_dd'_asym_le_Mfst_d  f); apply (le_p1_asym Hd).
    intro f; rewrite (Msnd_dd'_asym_le_Msnd_d' f); apply (le_p2_asym Hd').
 Qed.


End ASYM_LIFT_TRANS.

 
End LE_LIFT_ASYM.

End Asym_lift.

Add Parametric Morphism A B : (le_lift_asym (A:=A) (B:=B))
 with signature Fimp2 (A:=A) (B:=B) --> 
  Oeq (O:=Distr (A * B)) ==> Oeq (O:=Distr A) ==> 
  Oeq (O:=Distr B) ==> (@eq R) ==> Oeq (O:=U) ==> inverse impl
  as elift_asym_morph.
Proof.
 unfold impl, Fimp2; intros R1 R2 H d1 d2 H0 d3 d4 H1 d5 d6 H2 ep lam1 lam2 H3 H4.
 eapply le_lift_asym_weaken. 
 apply H.
 trivial.
 rewrite H3; trivial.
 eapply le_lift_asym_eq_compat with d2 d4 d6 ep lam2; auto.
Qed.
