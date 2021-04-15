theory Protocol_Parameters
imports Complex_Main
begin

locale protocol_parameters =
  fixes k :: nat
    and f :: real
  assumes k_positivity: "k > 0"
    and f_non_zero_probability: "f \<in> {0<..1}"
begin

abbreviation default_window_size :: nat where
  "default_window_size \<equiv> nat \<lceil>3 * k / f\<rceil>"

lemma default_window_size_positivity:
  shows "default_window_size > 0"
  using f_non_zero_probability and k_positivity by force

end

end

