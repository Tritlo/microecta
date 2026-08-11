# Future work
+ Generate from arbitrary ECTAs with direct counting and unranking of finite equality-constrained automata, eventually extending that boundary to bounded recursive languages.
+ Extend structural rank shrinking (shrinkRank factors ranks through the plan) to globally minimal counterexamples: size-stratified counting per plan node (FEAT-style convolution) enumerates the language in size order, turning shrinking into a search for the smallest failing member. Term-level shrink rewrites validated by nodeRepresents against the support are the complementary route.
