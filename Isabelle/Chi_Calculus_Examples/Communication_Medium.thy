theory Communication_Medium
  imports
    "HOL-Library.BNF_Corec"
    Chi_Calculus.Typed_Processes
begin

corec
  sender :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "sender inp inpm = inp \<triangleright>\<degree> x. (inpm \<triangleleft>\<degree> x \<parallel> sender inp inpm)"

corec
  receiver :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "receiver outm out = outm  \<triangleright>\<degree> x. (out \<triangleleft>\<degree> x \<parallel> receiver outm out)"

corec
  medium :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "medium inpm outm = inpm \<triangleright>\<degree> x. (outm \<triangleleft>\<degree> x \<parallel> medium inpm outm)"

abbreviation
  impl :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "impl inp out \<equiv> \<nu>\<degree> inpm outm. (sender inp inpm \<parallel> medium inpm outm \<parallel> receiver outm out)"

corec
  spec :: "['a::countable channel, 'a::countable channel] \<Rightarrow> process"
where
  "spec inp out = inp \<triangleright>\<degree> x. (out \<triangleleft>\<degree> x \<parallel> spec inp out)"

end
