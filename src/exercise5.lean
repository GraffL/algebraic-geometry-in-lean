import order.galois_connection
import exercise4

universe u

-- exercise 5(a)
-- Show that in a galois connection fg the right adjoint g preserves meets

lemma gPreservesMeets {A B : Type u} {f: A → B} {g: B → A} [partial_order A] [partial_order B] [gc : galois_connection f g] 
      (M : set B) (m : B) (h : isMeet M m) : (isMeet {a : A | ∃ b ∈ M, g b = a} (g m) ) :=
begin
  split,
  {
    intros n hn,
    cases hn with b hb,
    cases hb with b_in_M gb_is_n,
    have b_ge_n : b ≥ m := begin
      apply h.left,
      exact b_in_M,
    end,
    have gb_ge_gn : g b ≥ g m := begin
      apply gc.monotone_u,
      assumption,
    end,
    calc n  = g b : by rw gb_is_n
        ... ≥ g m : by exact gb_ge_gn
  },
  {
    intro a',
    intro ha',
    change a' ≤ g m,
    rw ← gc,
    apply h.right,
    intros b b_in_M,
    change f a' ≤ b,
    rw gc,
    apply ha',
    use b,
    use b_in_M,
  }
end

-- exercise 5(b)
-- Show that in a galois connection fg the left adjoint f preserves joins
lemma fPreservesJoins {A B : Type u} {f: A → B} {g: B → A} [partial_order A] [partial_order B] [gc : galois_connection f g] 
      (N : set A) (n : A) (h : isJoin N n) : (isJoin {b : B | ∃ a ∈ N, f a = b} (f n) ) :=
begin
  split,
  {
    intros m hm,
    cases hm with a ha,
    cases ha with a_in_N fa_is_m,
    have a_le_n : a ≤ n := begin
      apply h.left,
      exact a_in_N,
    end,
    have fa_le_fn : f a ≤ f n := begin
      apply gc.monotone_l,
      assumption,
    end,
    calc m  = f a : by rw fa_is_m
        ... ≤ f n : by exact fa_le_fn
  },
  {
    intro b',
    intro hb',
    rw gc,
    apply h.right,
    intros a a_in_N,
    rw ← gc,
    apply hb',
    use a,
    use a_in_N,
  }
end
