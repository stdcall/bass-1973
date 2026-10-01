#import "main-defs.typ": (
  Cart, Coker, Div, End, Frac, Hom, Ht, Im, Int, Ker, Pic, PicCat, U, ann, dim,
  hd, ht, idx, maxSpec, moduleCategory, name-idx, nil, rad, source, spec, supp,
  symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, numbered-condition, proof,
  proposition, theorem, variant-condition,
)
#import "diagrams/rings-modules-diagrams.typ": (
  divisor-class-square, fractional-submodule-isomorphisms,
  localized-divisor-class-square,
)

== Ранг, группа Pic и кольца Крулля
<sec:rank-picard-krull>

#source(114) В этом параграфе все кольца коммутативны.

#theorem[
  Пусть $A$ — коммутативное кольцо. Следующие условия на
  $P in moduleCategory hyph A$ эквивалентны:
  #condition-list[
    #condition-item[$P in bold(P)(A)$;] <cond:finite-projective-module>

    #condition-item[модуль $P$ конечно представим и $P_(frak(m))$ — свободный
      $A_(frak(m))$-модуль для всех
      $frak(m) in maxSpec(A)$;] <cond:projective-finite-presentation-local-free>

    #condition-item[модуль $P$ конечно порожден, и $P_(frak(p))$ — свободный
      $A_(frak(p))$-модуль для всех $frak(p) in spec(A)$; если $r_(frak(p))$ —
      число элементов $A_(frak(p))$-базиса модуля $P_(frak(p))$, то отображение
      $frak(p) arrow.r.bar r_(frak(p))$ является непрерывной (т. е. локально
      постоянной) функцией из $spec(A)$ в $Int$ (с дискретной
      топологией).] <cond:projective-local-free-continuous-rank>
  ]
] <th:projective-local-free-rank>
#proof[
  $#[@cond:finite-projective-module] =>
  #[@cond:projective-finite-presentation-local-free]$. Очевидно, что модуль $P$
  конечно представим, и в силу следствия @cor:local-projective-free
  $A_(frak(m))$-модуль $P_(frak(m))$ является свободным.

  $#[@cond:projective-finite-presentation-local-free] =>
  #[@cond:projective-local-free-continuous-rank]$. Ясно, что модуль $P$ конечно
  порожден. Если $frak(p) in spec(A)$, то можно вложить $frak(p)$ в
  $frak(m) in maxSpec(A)$. Тогда $P_(frak(p))$ является локализацией модуля
  $P_(frak(m))$ и, следовательно, свободным модулем.

  Пусть $n = r_(frak(p))$. Так как $P_(frak(p)) approx.eq A_(frak(p))^n$, то
  можно выбрать гомоморфизм $d\: A^n arrow.r P$, такой, что $d_(frak(p))$ —
  изоморфизм. Мы хотели бы показать, что $d_(frak(q))$ является изоморфизмом для
  всех $frak(q)$ в некоторой окрестности точки $frak(p)$. Если рассмотреть $d$
  как дифференцирование комплекса $C$ (с двумя ненулевыми членами), то в силу
  предложения @prop:closed-support-finite-complex $supp(H(C))$ — замкнутое
  множество. Если $frak(q) in.not supp(H(C))$, то комплекс $C_(frak(q))$
  ацикличен, т. е. $d_(frak(q))$ — изоморфизм.

  $#[@cond:projective-local-free-continuous-rank] =>
  #[@cond:projective-finite-presentation-local-free]$. Если
  $frak(p) in spec(A)$, то, как и выше, можно построить гомоморфизм
  $d\: A^n arrow.r P$, такой, что $d_(frak(p))$ — изоморфизм. Покажем, что
  $d_(frak(q))$ является изоморфизмом и в некоторой окрестности точки $frak(p)$.
  Так как модуль $P$ конечно порожден, то $Coker(d)_s = 0$ для некоторого
  $s in.not frak(p)$. Кроме того, в силу предположения $r_(frak(q)) = n$ для
  всех $frak(q)$ из некоторой окрестности точки $frak(p)$. Если $V(frak(a))$ —
  дополнение этой окрестности, то можно выбрать $t in frak(a)$,
  $t in.not frak(p)$. Если $U$ — дополнение к $V(s t)$, то отображение
  $d_(frak(q))$ сюръективно для всех $frak(q) in U$ (поскольку
  $s in.not frak(q)$) и $r_(frak(q)) = n$ (поскольку $t in.not frak(q)$ и,
  следовательно, $frak(a) subset.not frak(q)$). Но эпиморфизм
  $A_(frak(q))^n arrow.r A_(frak(q))^n$ является изоморфизмом, поэтому
  $d_(frak(q))$ — изоморфизм для всех $frak(q) in U$.

  С учетом этого условие $#[@cond:projective-finite-presentation-local-free]$
  будет доказано, как только мы докажем следующее утверждение: если для любого
  $frak(p) in spec(A)$ существует элемент $s in.not frak(p)$, такой, что
  $S^(-1)P$ является конечно представимым $S^(-1)A$-модулем, где
  $S = {s^n | n >= 0}$, то $A$-модуль #source(115) $P$ конечно представим. (В
  рассмотренном выше случае воспользуемся построенным элементом $s t$, при этом
  $S^(-1)P approx.eq (S^(-1)A)^n$.)

  Для доказательства этого утверждения воспользуемся квазикомпактностью
  пространства $spec(A)$ (см. предложение @prop:prime-spectrum-topology) и
  найдем элементы $s_1,dots,s_n$, такие, что модуль $S_i^(-1)P$ конечно
  представим для каждого $i$, где $S_i = {s_i^n}$, и что дополнения к $V(s_i)$
  накрывают $spec(A)$. Пусть
  $ 0 arrow.r K arrow.r A^m arrow.r P arrow.r 0 $
  — точная последовательность. Тогда модуль $S_i^(-1)K$ конечно порожден, и,
  значит, найдется конечное множество $X_i subset K$, образ которого в
  $S_i^(-1)K$ порождает $S_i^(-1)K$ как $S_i^(-1)A$-модуль. Тогда подмодуль
  $M subset K$, порожденный множеством $union_i X_i$, таков, что
  $M_(frak(p)) = K_(frak(p))$ для всех $frak(p)$ и, следовательно, $M = K$.

  $#[@cond:projective-finite-presentation-local-free] =>
  #[@cond:finite-projective-module]$. По предположению
  $U_0(P) = {frak(p) | hd_(A_(frak(p)))(P_(frak(p))) <= 0} = spec(A)$, и в силу
  предложения @prop:projective-dimension-open-locus (которое применимо,
  поскольку модуль $P$ конечно представим) $P in bold(P)(A)$, что и требовалось
  доказать.
]

Если $P in bold(P)(A)$, то через
$ [P\:A]\: spec(A) arrow.r Int $
обозначим непрерывную функцию, описанную в условии
@cond:projective-local-free-continuous-rank, и назовем ее _рангом_ модуля $P$.
#idx("ранг модуля") Введем также обозначение
$ P^* = Hom_A (P,A). $
Для любого модуля $M$ рассмотрим отображение
$h_P\: P^* tensor_A M arrow.r Hom_A (P,M)$, определенное равенством
$h_P (f tensor m)(x) = m f(x)$. Оно является естественным преобразованием.
Очевидно, что $h_A$ — изоморфизм, и поэтому в силу аддитивности $h_P$ —
изоморфизм для любого $P in bold(P)(A)$.

#proposition[
  Пусть $P,Q in bold(P)(A)$. Тогда
  $ [P^*\:A] = [P\:A], $
  $ [P plus.o Q\:A] = [P\:A] + [Q\:A] $
  и
  $ [P tensor_A Q\:A] = [Hom_A (P,Q)\:A] = [P\:A][Q\:A]. $
  Кроме того, модуль $P$ точен (и, следовательно, строго проективный (см.
  @ch:module-categories, § @sec:module-category-characterization)) тогда и
  только тогда, когда функция $[P\:A]$ всюду положительна.
] <prop:projective-rank-formulas>
#proof[
  Формулы очевидны. Множество точек, где $[P\:A]$ отлично от нуля, совпадает с
  $supp(P) = V(ann(P))$. Предложение доказано.
]

#source(116)
#proposition[
  Пусть $f\: A arrow.r B$ — гомоморфизм коммутативных колец, индуцирующий
  отображение $attach(f, tl: a)\: spec(B) arrow.r spec(A)$. Пусть
  $P in bold(P)(A)$ и $M in moduleCategory hyph A$. Тогда естественные
  гомоморфизмы
  $ (P tensor_A M) tensor_A B arrow.r (P tensor_A B) tensor_B (M tensor_A B) $
  и
  $ Hom_A (P,M) tensor_A B arrow.r Hom_B (P tensor_A B,M tensor_A B) $
  являются изоморфизмами. Кроме того,
  $ [P tensor_A B\:B] = [P\:A] compose attach(f, tl: a). $
] <prop:projective-base-change-rank>
#proof[
  Изоморфизм тензорных произведений хорошо известен (и имеет место без всяких
  ограничений на $P$). Изоморфизм в случае функтора $Hom$ следует в силу
  аддитивности из частного случая $P = A$, в котором результат очевиден.

  Если $frak(q) in spec(B)$ и
  $frak(p) = attach(f, tl: a)(frak(q)) = f^(-1)(frak(q))$, то $B_(frak(q))$
  является локализацией $A_(frak(p))$-алгебры $B_(frak(p))$. Так как
  $P_(frak(p))$
  — свободный $A_(frak(p))$-модуль, то
  $(P_(frak(p)) tensor_(A_(frak(p))) B_(frak(p))) = (P tensor_A
    B)_(frak(p))$, при этом модуль $(P tensor_A B)_(frak(p))$ и его локализация
  $(P tensor_A B)_(frak(q))$ являются свободными модулями одного и того же ранга
  соответственно над $B_(frak(p))$ и $B_(frak(q))$. Таким образом,
  $ [(P tensor_A B)_(frak(q))\:B_(frak(q))] = [P_(frak(p))\:A_(frak(p))]. $
  Предложение доказано.
]

#proposition[
  Предположим, что $P,Q in moduleCategory hyph A$ и что
  $P tensor_A Q approx.eq A^n$ для некоторого $n > 0$. Тогда $P,Q$ принадлежат
  $bold(P)(A)$ и являются строго проективными модулями.
] <prop:tensor-free-factors-projective>
#proof[
  Если элементы ${x_i tensor y_i | 1 <= i <= m}$ порождают модуль $P tensor_A Q$
  (являющийся конечно порожденным), то определим $h\: A^m arrow.r P$, переводя
  базисные элементы в $x_i$. Тогда отображение
  $h tensor_A Q\: A^m tensor_A Q arrow.r P tensor_A Q approx.eq A^n$ сюръективно
  и, следовательно, расщепляется. Аналогично $h tensor_A Q tensor_A P$ —
  расщепляющийся эпиморфизм. Но последний эпиморфизм изоморфен прямой сумме $n$
  экземпляров отображения $h$, поэтому $h$ — расщепляющийся эпиморфизм. Это
  показывает, что $P in bold(P)(A)$ и, симметрично, $Q in bold(P)(A)$. Кроме
  того, эти модули точные, поскольку модуль $P tensor_A Q$ точен.
]

Перейдем теперь к изучению категории
$ PicCat(A) = PicCat_A (A), $
введенной в (@ch:module-categories, § @sec:picard-group), где упор был сделан на
двусторонних $A$-модулях. Сейчас мы рассматриваем $A$ как $A$-алгебру, и это
означает, что элементы из $A$ действуют на объектах категории $PicCat(A)$
одинаково справа и слева. Следовательно, объекты этой категории #source(117)
можно рассматривать просто как правые $A$-модули. В таком случае условие, что
$P in moduleCategory hyph A$ принадлежит к $PicCat(A)$, означает, что модуль $P$
_обратим_, в том смысле, что существует $Q in moduleCategory hyph A$, для
которого $P tensor_A Q approx.eq A$. В этом случае теория, развитая в гл.
@ch:module-categories, показывает, что $Q approx.eq Hom_A (P,A) = P^*$. Кроме
того, классы $[P]$ изоморфных обратимых модулей образуют группу
$ Pic(A) $
с умножением $[P][Q] = [P tensor_A Q]$.

#proposition[
  Следующие условия на $P in moduleCategory hyph A$ эквивалентны:
  #condition-list[
    #condition-item[модуль $P$ обратим, т. е.
      $P in PicCat(A)$;] <cond:invertible-module>

    #condition-item[$P in bold(P)(A)$ и
      $[P\:A] = 1$;] <cond:invertible-module-projective-rank-one>

    #variant-condition[$P in bold(P)(A)$ и
      $End_A (P) = A$;] <cond:invertible-module-endomorphisms>

    #condition-item[$P in bold(M)(A)$ и $P_(frak(m)) approx.eq A_(frak(m))$ для
      всех $frak(m) in maxSpec(A)$.] <cond:invertible-module-locally-free-one>
  ]
] <prop:invertible-module-characterizations>
#proof[
  $#[@cond:invertible-module] =>
  #[@cond:invertible-module-projective-rank-one]$. Так как
  $P^* tensor_A P approx.eq A$, то в силу предложения
  @prop:tensor-free-factors-projective $P in bold(P)(A)$ и
  $[P^*\:A][P\:A] = [P\:A]^2 = 1$. Так как функция $[P\:A]$ принимает
  неотрицательные целые значения, то $[P\:A] = 1$.

  $#[@cond:invertible-module-projective-rank-one] =>
  #[@cond:invertible-module-endomorphisms]$. Если $[P\:A] = 1$, то включение
  $A subset End_A (P)$ локально превращается в равенство и, следовательно,
  является равенством.

  $#[@cond:invertible-module-endomorphisms] =>
  #[@cond:invertible-module-locally-free-one]$.
  $P_(frak(m)) approx.eq A_(frak(m))^n$ для некоторого $n > 0$, а из равенства
  $A_(frak(m)) = End_(A_(frak(m)))(P_(frak(m)))$ следует, что $n = 1$.

  $#[@cond:invertible-module-locally-free-one] => #[@cond:invertible-module]$.
  Локализуя сначала по некоторому $frak(m) in maxSpec(A)$, содержащему
  $frak(p)$, убеждаемся в том, что $P_(frak(p)) approx.eq
  A_(frak(p))$ для всех $frak(p) in spec(A)$. Из теоремы
  @th:projective-local-free-rank следует, что $P in bold(P)(A)$. Пусть
  $h\: P^* tensor_A P arrow.r A$, где $h(f tensor x) = f(x)$. Так как модуль $P$
  конечно представим, то можно отождествить $(P^*)_(frak(p))$ с
  $(P_(frak(p)))^*$, и поэтому $h_(frak(p))$ является изоморфизмом для всех
  $frak(p) in spec(A)$. Следовательно, $h$ — изоморфизм, поэтому
  $P in PicCat(A)$.
]

#corollary[
  Гомоморфизм $A arrow.r B$ коммутативных колец индуцирует функтор
  $tensor_A B\: PicCat(A) arrow.r PicCat(B)$, переводящий $tensor_A$ в
  $tensor_B$ и, следовательно, индуцирующий также гомоморфизм
  $Pic(A) arrow.r Pic(B)$ (это превращает $Pic$ в функтор).
] <cor:picard-base-change-functor>
#proof[Утверждение следует из @prop:projective-base-change-rank и критерия
  @cond:invertible-module-projective-rank-one, приведенного выше.]

Пусть теперь $S$ — мультипликативная система неделителей нуля в $A$. Если $M$
есть $A$-подмодуль в $S^(-1)A$, то рассмотрим индуцированный мономорфизм
$S^(-1)M arrow.r S^(-1)A$, являющийся изоморфизмом в точности тогда, когда $M$
порождает $S^(-1)A$ как $S^(-1)A$-модуль, т. е. когда $(S^(-1)A)M = S^(-1)A$. В
этом случае $1 = (a slash s)x$ #source(118) для некоторого $x in M$ и,
следовательно, $s = a x in M inter S$. Обратно, если $M inter S != emptyset$, то
очевидно, что $(S^(-1)A)M = S^(-1)A$. Если модуль $M$ удовлетворяет этим
равносильным условиям, то мы назовем $M$ _невырожденным_ $A$-подмодулем в
$S^(-1)A$. #idx("невырожденный модуль")

Если $M$ и $N$ — невырожденные подмодули и, скажем, $s in M inter S$ и
$t in N inter S$, то $s t$ лежит в каждом из модулей $M + N$, $M inter N$ и
$M dot N$ (последнее обозначает подмодуль, порожденный всеми элементами $x y$,
где $x in M$, $y in N$).

Определим
$ (N\:M) = {b in S^(-1)A | b M subset N}. $
Если $b in N\:M$, то равенство $h_b (x) = b x$ определяет элемент
$h_b in Hom_A (M,N)$ и, следовательно, отображение $(N\:M) arrow.r Hom_A (M,N)$,
являющееся, очевидно, гомоморфизмом. Если $h_b = 0$, то $b = 0$, поскольку $b$
аннулирует неделитель нуля из $S inter M$. Кроме того, если $h in Hom_A (M,N)$,
то $S^(-1)h in Hom_(S^(-1)A)(S^(-1)M,S^(-1)N) approx.eq
Hom_(S^(-1)A)(S^(-1)A,S^(-1)A) = S^(-1)A$. Таким образом, $S^(-1)h(x) = b x$ для
некоторого $b in S^(-1)A$. Так как $S^(-1)h(M) subset N$, то $b in N\:M$, и,
следовательно, $h = h_b$.

Подводя итог, получаем #proposition[
  Если $M$ и $N$ — невырожденные подмодули в $S^(-1)A$, то естественный
  гомоморфизм $(N\:M) arrow.r Hom_A (M,N)$ биективен. Если $(A\:M)$ также
  невырожденен, то вложение $M subset (A\:(A\:M))$ изоморфно естественному
  гомоморфизму $M arrow.r M^(**)$. Кроме того, в этом случае модуль $M^*$
  рефлексивен.
] <prop:fractional-submodule-hom-duality>
Для доказательства последнего утверждения можно отождествить $M^*$ с $(A\:M)$.
Если $M subset N$, то $N^* subset M^*$. Таким образом, так как
$M subset M^(**)$, то $M^* subset (M^*)^(**) = (M^(**))^* subset M^*$.

Назовем $A$-подмодуль $M subset S^(-1)A$ _обратимым подмодулем_ в $S^(-1)A$,
если $M dot N = A$ для некоторого $N subset S^(-1)A$. Очевидно, что тогда $M$ и
$N$ должны быть невырожденными. Если выбрать $s in S inter M inter N$, то
$M s subset M N = A$, и поэтому
$ A s subset M subset A s^(-1). $
В том случае, когда $S$ — множество всех неделителей нуля, назовем кольцо
$S^(-1)A$ _полным кольцом частных_ кольца $A$. Идеал $frak(a) subset A$ назовем
_обратимым идеалом_, если он обратим в полном кольце частных. #idx(
  "обратимый подмодуль",
)#idx("полное кольцо частных")#idx("обратимый идеал")

#theorem[
  Пусть $M$ — невырожденный $A$-подмодуль в $S^(-1)A$. Тогда следующие условия
  эквивалентны:
  #condition-list[
    #condition-item[$M$ — обратимый подмодуль в
      $S^(-1)A$;] <cond:invertible-fractional-submodule>

    #condition-item[
      $M in bold(P)(A)$;
    ] <cond:fractional-submodule-finite-projective>

    #condition-item[$M in PicCat(A)$;] <cond:fractional-submodule-picard-object>

    #condition-item[$M in bold(M)(A)$ и модуль $M_(frak(m))$ порождается одним
      элементом для любого
      $frak(m) in maxSpec(A)$.] <cond:fractional-submodule-locally-cyclic>
  ]
] <th:invertible-fractional-submodule-characterizations>
#proof[
  #source(119)
  $#[@cond:invertible-fractional-submodule] =>
  #[@cond:fractional-submodule-finite-projective]$. Если $M N = A$, то можно
  записать $1 = sum_i m_i n_i$, где $m_i in M$ и $n_i in N$. Определим
  $h_i\: M arrow.r A$, полагая $h_i (m) = n_i m$. Тогда
  $m = sum_i m_i n_i m = sum_i m_i h_i (m)$ для любого $m in M$, и поэтому в
  силу предложения @prop:projective-dual-basis $M in bold(P)(A)$.

  $#[@cond:fractional-submodule-finite-projective] =>
  #[@cond:fractional-submodule-picard-object]$. Так как $S^(-1)M = S^(-1)A$, то
  $T^(-1)M approx.eq T^(-1)A$, где $T = {t^n | n >= 0}$ для некоторого $t in S$.
  Если нам дан $frak(p) in spec(A)$, то найдется простой идеал
  $frak(q) subset frak(p)$, такой, что $t in.not frak(q)$. Действительно, в
  противном случае элемент $t slash 1$ лежал бы в силу предложения
  @prop:radical-ideal-prime-intersection в $nil A_(frak(p))$, и тогда
  $t^n s = 0$ для некоторого $n >= 0$ и $s in.not frak(p)$, но это противоречит
  тому, что $t$ не является делителем нуля. Так как
  $A_(frak(q)) = (A_(frak(p)))_(frak(q)_(frak(p)))$, то
  $[M_(frak(p))\:A_(frak(p))] = [M_(frak(q))\:A_(frak(q))]$. Поскольку
  $T inter frak(q) = emptyset$, модуль $A_(frak(q))$ является локализацией
  модуля $T^(-1)A$, поэтому $[M_(frak(q))\:A_(frak(q))] = 1$.

  Импликации
  $#[@cond:fractional-submodule-picard-object] =>
  #[@cond:fractional-submodule-finite-projective]$
  и
  $#[@cond:fractional-submodule-picard-object] =>
  #[@cond:fractional-submodule-locally-cyclic]$
  очевидны. Для окончания доказательства надо показать, что
  $#[@cond:fractional-submodule-locally-cyclic] =>
  #[@cond:fractional-submodule-picard-object]$
  и $#[@cond:fractional-submodule-finite-projective] =>
  #[@cond:invertible-fractional-submodule]$.

  $#[@cond:fractional-submodule-locally-cyclic] =>
  #[@cond:fractional-submodule-picard-object]$. Так как модуль $M$
  невырожденный, то он точный $A$-модуль. Модуль $M_(frak(m))$ также точный
  $A_(frak(m))$-модуль, поскольку $M$ — конечно порожденный модуль.
  Действительно, если $X$ — конечная система образующих модуля $M$ и если
  элемент $a slash s in A_(frak(m))$ аннулирует модуль $M_(frak(m))$, то
  множество $X a$ аннулируется некоторым элементом $t in.not frak(m)$ (поскольку
  множество $X a$ конечно и переходит в нуль в $M_(frak(m))$). Таким образом,
  $a t in ann_A (M) = 0$ и, следовательно, $a slash s = (a t) slash (s t) = 0$.

  В силу предположения модуль $M_(frak(m))$ циклический. Так как он точен, он
  изоморфен модулю $A_(frak(m))$.

  $#[@cond:fractional-submodule-finite-projective] =>
  #[@cond:invertible-fractional-submodule]$. В силу предложения
  @prop:fractional-submodule-hom-duality можем отождествить $M^*$ с $(A\:M)$.
  Таким образом, если $M in bold(P)(A)$, то из предложения
  @prop:projective-dual-basis следует, что найдутся элементы $m_i in M$,
  $n_i in (A\:M)$ ($i in I$) для некоторого конечного множества $I$, такие, что
  $m = sum_i m_i n_i m$ для всех $m in M$. Так как модуль $M$ точен, то
  $sum_i m_i n_i = 1$ и потому $M(A\:M) = A$, что и требовалось доказать.
]

#proposition[
  Пусть $M$ и $N$ — два $A$-подмодуля в $S^(-1)A$ и $M$ — обратимый модуль.
  Тогда $N = (N\:M)M$, $(N\:M) = N(A\:M)$ и естественный гомоморфизм
  $ M tensor_A N arrow.r M N $
  является изоморфизмом.
] <prop:invertible-submodule-product-tensor>
#proof[
  Пусть $i\: N arrow.r S^(-1)A$ — вложение. Так как модуль $M$ проективен, то
  отображение $M tensor_A N arrow.r M tensor_A S^(-1)A$ — мономорфизм. Можно
  отождествить $M tensor_A S^(-1)A$ с $S^(-1)A$, и тогда образ модуля
  $M tensor_A N$ совпадает с $M N$.

  Пусть $M' = (A\:M)$. Тогда очевидно, что $M'N subset N\:M$ и
  $M(N\:M) subset N$. Таким образом, поскольку $M M' = A$, то #source(120)
  $(N\:M) = M'M(N\:M) subset M'N$ и $N = M M'N subset M(N\:M)$, что завершает
  доказательство.
]

Обозначим через
$ Pic(A, S) $
множество обратимых $A$-подмодулей в $S^(-1)A$. Оно является группой
относительно умножения. Кроме того, если $M in Pic(A, S)$, то в силу теоремы
@th:invertible-fractional-submodule-characterizations $M$ принадлежит
$PicCat(A)$ и, согласно предложению @prop:invertible-submodule-product-tensor,
отображение $Pic(A, S) arrow.r Pic(A)$, при котором $M arrow.r.bar [M]$,
является гомоморфизмом. Если $b in U(S^(-1)A)$, то модуль $A b$ обратим и
$A\:A b = A b^(-1)$. Таким образом, получаем гомоморфизм
$U(S^(-1)A) arrow.r Pic(A, S)$.
#symbol-idx($Pic$, sort: "Pic", group: "operators", order: 66)

#proposition[
  Пусть, как и раньше, $S$ — мультипликативная система неделителей нуля в $A$.
  Тогда последовательность
  $
    0 arrow.r U(A) arrow.r U(S^(-1)A) arrow.r Pic(A, S) arrow.r Pic(A)
    arrow.r Pic(S^(-1)A)
  $
  точна.
] <prop:picard-localization-exact-sequence>
#proof[
  Поскольку отображение $A arrow.r S^(-1)A$ инъективно, инъективно и отображение
  $U(A) arrow.r U(S^(-1)A)$. Если $b in U(S^(-1)A)$, то очевидно, что
  $b A = A <=> b in U(A)$.

  Если $M in Ker(Pic(A, S) arrow.r Pic(A))$, то можно выбрать элементы
  $b' in A\:M approx.eq Hom_A (M,A)$ и $b in M\:A approx.eq Hom_A (A,M)$,
  индуцирующие взаимно обратные изоморфизмы
  #fractional-submodule-isomorphisms()
  Отсюда следует, что $M = b A$ и $b b' = 1$, поэтому $b in U(S^(-1)A)$.

  Если $M in Pic(A, S)$, то $S^(-1)M = S^(-1)A$, так что
  $[M] in Ker(Pic(A) arrow.r Pic(S^(-1)A))$. Обратно, если $P$ лежит в этом
  ядре, то выберем $h\: P arrow.r A$ так, чтобы $S^(-1)h$ было бы изоморфизмом.
  Так как $S$ состоит из неделителей нуля и $P in bold(P)(A)$, то отображение
  $P arrow.r S^(-1)P$ инъективно и, следовательно, отображение $h$ также
  инъективно. Таким образом, $P approx.eq h P subset S^(-1)A$. В силу теоремы
  @th:invertible-fractional-submodule-characterizations $h P in Pic(A, S)$, что
  заканчивает доказательство предложения.
]

Пусть теперь $A$ — область целостности и $S = A without {0}$. В этом случае
$L = S^(-1)A$ является полем частных кольца $A$. Так как очевидно, что
$Pic(L) = 0$, то из теоремы
@th:invertible-fractional-submodule-characterizations и предложения
@prop:picard-localization-exact-sequence следует, что идеал $a subset A$ обратим
как $A$-модуль тогда и только тогда, когда он обратим как подмодуль в $L$ (в том
смысле, который обсуждался выше). Будем в этом случае говорить, что $a$ —
_обратимый идеал_. Кольцо $A$ называется _дедекиндовым_,#idx(
  "дедекиндово кольцо",
) если каждый #source(
  121,
) ненулевой идеал в $A$ обратим, и называется _кольцом дискретного
нормирования_, если оно является локальным дедекиндовым кольцом. Например,
область главных идеалов является дедекиндовым кольцом.
#idx("кольцо дискретного нормирования")

#proposition[
  Следующие условия на локальное кольцо $A$ с максимальным идеалом
  $frak(p) != 0$ эквивалентны:
  #condition-list[
    #condition-item[$A$ — кольцо дискретного
      нормирования;] <cond:discrete-valuation-ring>

    #condition-item[
      кольцо $A$ нётерово и $frak(p) in bold(P)(A)$;
    ] <cond:discrete-valuation-noetherian-projective-maximal-ideal>

    #condition-item[$A$ — область целостности, идеал $frak(p) = p A$ является
      главным и $U(L) = U(A) times {p^n | n in Int}$, где $L$ — поле частных
      кольца $A$.] <cond:discrete-valuation-principal-maximal-ideal>
  ]
] <prop:discrete-valuation-ring-characterizations>
#proof[
  $#[@cond:discrete-valuation-ring] =>
  #[@cond:discrete-valuation-noetherian-projective-maximal-ideal]$. Каждый
  обратимый модуль лежит в $bold(P)(A)$, поэтому кольцо $A$ нётерово и
  $frak(p) in bold(P)(A)$.

  $#[@cond:discrete-valuation-noetherian-projective-maximal-ideal] =>
  #[@cond:discrete-valuation-principal-maximal-ideal]$. Так как кольцо $A$
  локально, то в силу следствия @cor:local-projective-free и нашего
  предположения о том, что $frak(p) != 0$, $frak(p) approx.eq A^n$ для
  некоторого $n > 0$. Поскольку никакие два элемента $a$ и $b$ из $A$ не могут
  быть линейно независимыми (действительно, $a b = b a$!), то $n = 1$. Таким
  образом, $frak(p) = p A approx.eq A$ и $p$ не является делителем нуля.
  Последнее свойство означает, что $p a = a$, где $a = inter_n p^n A$. Так как
  кольцо $A$ нётерово и $p in rad(A)$, то в силу леммы Накаямы $a = 0$. Если
  $a != 0$ в $A$, то пусть $n >= 0$ — наибольшее натуральное число, для которого
  $a in p^n A$. Как мы убедились, такое число $n$ существует. Запишем
  $a = u p^n$. Тогда $u in U(A)$, ибо в противном случае $u in p A$ и
  $a in p^(n+1)A$. Наконец, если $b = v p^m$, где $v in U(A)$, то
  $a b = u v p^(n+m) != 0$, и поэтому $A$ является областью целостности.
  Разложение $U(L) = U(A) times {p^n}$ легко получается из сделанных замечаний.

  $#[@cond:discrete-valuation-principal-maximal-ideal] =>
  #[@cond:discrete-valuation-ring]$. Очевидно, из условия
  $#[@cond:discrete-valuation-principal-maximal-ideal]$ следует, что каждый
  ненулевой идеал является главным и, следовательно, обратим, что и требовалось
  доказать.
]

Пусть $A$ и $frak(p)$ такие же, как в предложении
@prop:discrete-valuation-ring-characterizations. Если $frak(a) != 0$ есть
$A$-модуль в $L$, такой, что $d frak(a) subset A$ для некоторого элемента
$d != 0$ из $A$, то можно записать $d A = frak(p)^n$ и $d frak(a) = frak(p)^m$
для некоторых $n,m >= 0$, и тогда $frak(a) = frak(p)^(m-n) = p^(m-n)A$. Таким
образом, каждый такой $A$-модуль $frak(a)$ является степенью (положительной или
отрицательной) идеала $frak(p)$. Введем обозначения:
$
  v_(frak(p))(frak(p)^n) = n quad v_(frak(p))(x) = v_(frak(p))(x A) "для" x
  in U(L).
$
Таким образом, $v_(frak(p))\: U(L) arrow.r Int$ — гомоморфизм. Если мы определим
$v_(frak(p))(0) = infinity$, то с обычными соглашениями
$ v_(frak(p))(a+b) >= min(v_(frak(p))(a), v_(frak(p))(b)), $
(т. е. $a,b in frak(p)^n => a+b in frak(p)^n$), причем если $v_(frak(p))(a)$ и
$v_(frak(p))(b)$ различны, то имеет место равенство. Кроме того,
$A = {a | v_(frak(p))(a) >= 0}$ и $frak(p) = {a | v_(frak(p))(a) > 0}$.

#source(122) Заметим, что поскольку все ненулевые идеалы в $A$ имеют вид
$frak(p)^n$, то $spec(A) = {(0),frak(p)}$ и $dim A = 1$. Кроме того, если
$a = u p^(-n)$, где $n > 0$, то $A[a] = L$ и, следовательно, $a$ не является
целым элементом над $A$. Это показывает, что кольцо дискретного нормирования
целозамкнуто и его размерность $<= 1$. (Неравенство $<= 1$ позволяет включить
поля.)

#theorem[
  Пусть $A$ — область целостности. Тогда следующие условия эквивалентны:
  #condition-list[
    #condition-item[$A$ — дедекиндово кольцо;] <cond:dedekind-domain>

    #condition-item[кольцо $A$ наследственно (см.
      @prop:hereditary-ring-ideals);] <cond:dedekind-hereditary-domain>

    #condition-item[кольцо $A$ нётерово и $A_(frak(p))$ — кольцо дискретного
      нормирования при всех
      $frak(p) in maxSpec(A)$;] <cond:dedekind-noetherian-local-valuation>

    #condition-item[кольцо $A$ нётерово, целозамкнуто и
      $dim A <= 1$.] <cond:dedekind-noetherian-normal-dimension-one>
  ]
] <th:dedekind-domain-characterizations>
#proof[
  Эквивалентность условий $#[@cond:dedekind-domain]$ и
  $#[@cond:dedekind-hereditary-domain]$ следует в силу предложения
  @th:invertible-fractional-submodule-characterizations из предложения
  @prop:hereditary-ring-ideals.

  $#[@cond:dedekind-domain]$ и $#[@cond:dedekind-hereditary-domain] =>
  #[@cond:dedekind-noetherian-local-valuation]$. В силу предложения
  @th:invertible-fractional-submodule-characterizations обратимый идеал конечно
  порожден, и поэтому кольцо $A$ нётерово. В силу предложения
  @prop:localization-homological-dimension кольцо $A_(frak(p))$ наследственно
  для всех $frak(p)$.

  $#[@cond:dedekind-noetherian-local-valuation] =>
  #[@cond:dedekind-noetherian-normal-dimension-one]$. Кольцо $A_(frak(p))$
  является кольцом дискретного нормирования для каждого $frak(p) in maxSpec(A)$
  и, следовательно, является целозамкнутым кольцом, при этом его размерность
  $<= 1$ (в силу замечания, приведенного перед формулировкой теоремы). В
  частности, $ht(frak(p)) = dim(A_(frak(p))) <= 1$ для всех
  $frak(p) in maxSpec(A)$, и поэтому $dim A <= 1$. Покажем, что кольцо $A$
  целозамкнуто, заметив, что включение
  $ A subset B = inter_(frak(p) in maxSpec(A)) A_(frak(p)) $
  является равенством. Это вытекает из того, что
  $A_(frak(p)) subset B_(frak(p)) subset A_(frak(p))$ для всех
  $frak(p) in maxSpec(A)$.

  Импликация
  $#[@cond:dedekind-noetherian-normal-dimension-one] =>
  #[@cond:dedekind-domain]$
  будет доказана в более общем виде в § @sec:orders-semisimple-algebras, теорема
  @th:maximal-order-two-sided-lattices.
]

Пусть $A$ — область целостности с полем частных $L$. Через $Ht_1(A)$ обозначим
множество простых идеалов высоты один в $A$. Кольцо $A$ называется _кольцом
Крулля_, если оно удовлетворяет следующим условиям:
#condition-list[
  #condition-item[$A_(frak(p))$ — кольцо дискретного нормирования для всех
    $frak(p) in Ht_1(A)$;] <cond:krull-height-one-valuation>

  #condition-item[$A = inter_(frak(p)) A_(frak(p))$ ($frak(p) in Ht_1(A)$)
    (пересечение берется в $L$);] <cond:krull-height-one-intersection>

  #condition-item[ненулевой элемент $a$ из $A$ содержится лишь в конечном числе
    идеалов $frak(p) in Ht_1(A)$.] <cond:krull-finite-character>
]
#idx("кольцо Крулля")#symbol-idx(
  $Ht_1$,
  sort: "Ht_1",
  group: "operators",
  order: 53,
) Из условий @cond:krull-height-one-valuation и
@cond:krull-height-one-intersection следует, что кольцо $A$ целозамкнуто,
поскольку каждое из колец $A_(frak(p))$ целозамкнуто. Условие
@cond:krull-finite-character выполнено в любой нётеровой области целостности.
Действительно, тогда #source(123) идеалы $frak(p)$, высота которых равна единице
и которые содержат элемент $a$, соответствуют некоторой неприводимой компоненте
в $spec(A slash (a A))$. Так как кольцо $A slash (a A)$ нётерово, их число
конечно.

Приведем без доказательства следующий пример: #proposition[
  Нётерова целозамкнутая область целостности является кольцом Крулля.
] <prop:noetherian-normal-domain-krull>
Справедливость условия @cond:krull-finite-character была отмечена выше. Условие
@cond:krull-height-one-valuation выполняется в силу теоремы
@th:dedekind-domain-characterizations. Таким образом, не доказано лишь условие
@cond:krull-height-one-intersection. Однако, так как
$A = inter_(frak(m)) A_(frak(m))$ ($frak(m) in maxSpec(A)$) для любой области
целостности, то мы убеждаемся, что условие @cond:krull-height-one-intersection
выполняется автоматически в том случае, когда $dim A <= 1$, т. е. когда высота
каждого максимального идеала $<= 1$. Итак, мы доказали, что дедекиндово кольцо
является кольцом Крулля, размерность которого $<= 1$. Обратное утверждение будет
доказано позже @prop:one-dimensional-krull-dedekind.

Для кольца Крулля $A$ определим _группу дивизоров_ $D(A)$ как свободную абелеву
группу с базисом $Ht_1(A)$. Будем рассматривать $D(A)$ как частично
упорядоченную группу, в которой положительными элементами являются элементы с
положительными координатами в базисе $Ht_1(A)$. Назовем $A$-модуль
$frak(a) subset L$ _дробным идеалом_, если $d frak(a) subset A$ для некоторого
$d != 0$ в $A$. Через $Frac(A)$ обозначим множество ненулевых дробных идеалов.
Легко проверить, что если $frak(a),frak(b) in Frac(A)$, то $frak(a)+frak(b)$,
$frak(a) inter frak(b)$, $frak(a) frak(b)$ и
$(frak(a)\:frak(b)) = {x in L | x frak(b) subset frak(a)}$ также принадлежат к
$Frac(A)$. Имеет место естественное отображение
$ Div\: Frac(A) arrow.r D(A), $
$
  Div(frak(a)) = sum_(frak(p)) v_(frak(p))(frak(a))frak(p) quad (frak(p) in
    Ht_1(A)).
$
#idx("группа дивизоров")#idx("дробный идеал")
#symbol-idx($D(A)$, sort: "D(A)", group: "letters", order: 82)
#symbol-idx($Frac$, sort: "Frac", group: "operators", order: 48)
#symbol-idx($Div$, sort: "div", group: "operators", order: 41)
Здесь $v_(frak(p))$ является нормированием, ассоциированным с кольцом
дискретного нормирования $A_(frak(p))$:
$frak(a)_(frak(p)) = (frak(p)A_(frak(p)))^(v_(frak(p))(frak(a)))$. Из условия
@cond:krull-finite-character и замечания о том, что $d frak(a) subset A$ для
некоторого $d != 0$, легко вывести, что $v_(frak(p))(frak(a))$ определено и
равно нулю почти для всех $frak(p)$. Если $x in U(L)$, то мы используем более
короткое обозначение: $Div(x) = Div(x A)$.

Следующие формулы очевидны:
$
  Div(frak(a) frak(b)) = Div(frak(a)) + Div(frak(b)), \
  Div(frak(a)+frak(b)) = inf(Div(frak(a)), Div(frak(b))), \
  Div(frak(a) inter frak(b)) = sup(Div(frak(a)), Div(frak(b))).
$
Если $frak(a) in Frac(A)$, то положим
$breve(frak(a)) = inter_(frak(p)) frak(a)_(frak(p))$ (здесь предполагается, что
все $frak(p)$ пробегают множество $Ht_1(A)$). Назовем идеал $frak(a)$
_дивизориальным_, если $frak(a) = breve(frak(a))$.
#idx("дивизориальный идеал")
Так как $frak(a) subset breve(frak(a))$, то
$frak(a)_(frak(p)) subset breve(frak(a))_(frak(p)) subset frak(a)_(frak(p))$ для
всех $frak(p)$, #source(124) а потому
$breve(frak(a))_(frak(p)) = frak(a)_(frak(p))$ для всех $frak(p)$, и,
следовательно, идеал $breve(frak(a))$ является дивизориальным. Кроме того,
$Div(breve(frak(a))) = Div(frak(a))$, и так как $Div(frak(a))$ определяет идеал
$breve(frak(a))$, то
$Div(frak(a)) = Div(frak(b)) <=> breve(frak(a)) = breve(frak(b))$.

Если $frak(a),frak(b) in Frac(A)$, то
$(frak(a)\:frak(b))_(frak(p)) subset (frak(a)_(frak(p))\:frak(b)_(frak(p)))$ для
всех $frak(p)$ (всегда из $Ht_1(A)$), и поэтому
$breve((frak(a)\:frak(b))) subset
inter_(frak(p))(frak(a)_(frak(p))\:frak(b)_(frak(p)))$. Но
$[d frak(b) subset breve(frak(a))] <=> [d frak(b)_(frak(p)) subset
frak(a)_(frak(p))$
для всех $frak(p)] <=> [d frak(b) subset frak(a)_(frak(p))$ для всех
$frak(p)] <=> [d frak(b) subset breve(frak(a))]$, т. е.
$(breve(frak(a))\:frak(b)) =
inter_(frak(p))(frak(a)_(frak(p))\:frak(b)_(frak(p))) =
(breve(frak(a))\:breve(frak(b)))$. К тому же
$(breve(frak(a))\:frak(b)) subset breve((frak(a)\:frak(b))) subset
inter_(frak(p))(frak(a)_(frak(p))\:frak(b)_(frak(p))) =
inter_(frak(p))(frak(a)_(frak(p))\:frak(b)_(frak(p)))$. Сопоставляя эти
соотношения, получаем, что
$
  breve((frak(a)\:frak(b))) =
  inter_(frak(p))(frak(a)_(frak(p))\:frak(b)_(frak(p))) =
  (breve(frak(a))\:frak(b)) = (breve(frak(a))\:breve(frak(b))).
$
В частности,
$ Div(frak(a)\:frak(b)) = Div(frak(a)) - Div(frak(b)) $
и идеал $(frak(a)\:frak(b))$ является дивизориальным, если $frak(a)$ —
дивизориальный идеал. Из этой формулы следует, что $A\:frak(a)$ — дивизориальный
идеал и что $Div(A\:frak(a)) = -Div(frak(a))$, и поэтому
$ breve(frak(a)) = A\:(A\:frak(a)). $ <eq:divisorial-double-dual>

#proposition[
  Если $A$ — кольцо Крулля размерности $<= 1$, то $A$ — дедекиндово кольцо.
] <prop:one-dimensional-krull-dedekind>
#proof[
  Можно считать, что $A$ не является полем, и поэтому $Ht_1(A) = maxSpec(A)$.
  Следовательно, каждый идеал $frak(a) in Frac(A)$ дивизориальный и отображение
  $Div\: Frac(A) arrow.r D(A)$ является инъективным гомоморфизмом полугрупп. Так
  как $Im(Div)$ является группой, то группой является и $Frac(A)$, т. е. все
  идеалы $frak(a) in Frac(A)$ обратимы, что и требовалось доказать.
]

Из @eq:divisorial-double-dual следует, что группа $Cart(A)$ («дивизоров Картье»)
обратимых идеалов состоит из дивизориальных идеалов, и поэтому имеет место
мономорфизм $Cart(A) arrow.r D(A)$. Если $S = A without {0}$, то
$Cart(A) = Pic(A, S)$ в обозначениях предложения
@prop:picard-localization-exact-sequence. Следующая диаграмма с точными строками
коммутативна:
#numbered-condition[#divisor-class-square()] <eq:divisor-class-diagram>
#idx("дивизор Картье")#symbol-idx(
  $Cart$,
  sort: "Cart",
  group: "operators",
  order: 32,
) Нижняя строка является последовательностью из предложения
@prop:picard-localization-exact-sequence (учитывая, что $Pic(L) = 0$). Так как
отображение $Cart(A) arrow.r D(A)$ инъективно, инъективно также и отображение
$Pic(A) arrow.r C(A)$.

Пусть теперь $S$ — любая мультипликативная система в $A without {0}$. Тогда
легко видеть, что $S^(-1)A$ является кольцом Крулля, простые идеалы высоты один
которого соответствуют таким же идеалам #source(125) кольца $A$, не
пересекающимся с $S$. Осуществляя это отождествление, можно написать равенство
$ D(A) = D(S^(-1)A) plus.o D(A,S), $
где $D(A,S)$ — подгруппа, порожденная элементами множества
${frak(p) in Ht_1(A) | frak(p) inter S != emptyset}$. Теперь нетрудно показать,
что диаграмма
#numbered-condition[#localized-divisor-class-square()]
<eq:localized-divisor-class-diagram>
коммутативна, ее строки — точные последовательности и вертикальные отображения —
мономорфизмы. Точность нижней строчки следует из предложения
@prop:picard-localization-exact-sequence.

#proposition[
  Если рассмотренная выше система $S$ порождается элементами, которые порождают
  простые идеалы, то отображение $C(A) arrow.r C(S^(-1)A)$ является изоморфизмом
  и, следовательно, отображение $Pic(A) arrow.r Pic(S^(-1)A)$ (в диаграмме
  @eq:localized-divisor-class-diagram) — мономорфизм.
] <prop:prime-element-localization-class-group>
#proof[
  Пусть $(p_i)_(i in I)$ — образующие системы $S$, такие, что идеал $p_i A$
  прост. Если идеал $frak(p)$ простой и $frak(p) inter S != emptyset$, то
  $frak(p)$ содержит произведение элементов $p_i$ и, следовательно, некоторый
  $p_i$ принадлежит $frak(p)$. Так как идеал $p_i A$ простой, то
  $p_i A = frak(p)$, если $ht(frak(p)) = 1$, и поэтому
  $frak(p) in Im(U(S^(-1)A) limits(arrow.r)^(Div) D(A,S))$. Это верно для всех
  тех $frak(p)$, для которых отображение $Div$ сюръективно. Предложение вытекает
  теперь из свойств диаграммы @eq:localized-divisor-class-diagram.
]

Назовем кольцо $A$ _факториальным_, если $A$ — кольцо Крулля и $C(A) = 0$. #idx(
  "факториальное кольцо",
)

#proposition[
  Пусть $A$ — факториальное кольцо, и пусть идеал $frak(a) in Frac(A)$
  дивизориален. Тогда $frak(a)$ — главный идеал и
  $frak(a) = product_(frak(p)) frak(p)^(v_(frak(p))(frak(a)))$
  ($frak(p) in Ht_1(A)$).
] <prop:factorial-divisorial-ideal-principal>
#proof[
  Если $frak(p) in Ht_1(A)$, то $frak(p) = Div(a)$ для некоторого $a != 0$. Так
  как $a A$ и (очевидно) $frak(p)$ являются дивизориальными идеалами, то
  $frak(p) = a A$. Если $frak(a)$ — заданный идеал, то положим
  $frak(b) = product_(frak(p)) frak(p)^(v_(frak(p))(frak(a)))$. Тогда, как мы
  убедились, идеал $frak(b)$ главный и, следовательно, дивизориален. Так как
  $Div(frak(a)) = Div(frak(b))$ и в силу предположения, что идеал $frak(a)$
  дивизориален, $frak(a) = frak(b)$, что и требовалось доказать.
]

Пусть $A$ — произвольное коммутативное кольцо и $T$ — мультипликативная система
в $A$. Назовем систему $T$ _факториальной относительно_ $A$, если кольцо
$A_(frak(m))$ факториально для любого $frak(m) in maxSpec(A)$, такого, что
$frak(m) inter T != emptyset$.
#idx("факториальная относительно A система")

#source(126)
#proposition[
  Пусть $A$ — коммутативное нётерово кольцо и $T$ — мультипликативная система
  неделителей нуля, являющаяся факториальной относительно $A$. Тогда отображение
  $Pic(A) arrow.r Pic(T^(-1)A)$ сюръективно, и $Pic(A, T)$ является свободной
  абелевой группой с $M = {frak(p) in Ht_1(A) | frak(p) inter T != emptyset}$ в
  качестве базиса.
] <prop:factorial-localization-picard-surjection>
#proof[
  В доказательстве будем предполагать, что если $S$ — множество всех неделителей
  нуля, то $Pic(S^(-1)A) = 0$. Известно (см., например, Бурбаки
  @bib:Bourbaki1971b, § 5, № 7, замечание 2), что кольцо $S^(-1)A$ полулокально,
  а в предложении @prop:semilocal-picard-trivial мы покажем, что $Pic(B) = 0$
  для полулокального кольца $B$. Таким образом, наше предположение оправдано.

  Покажем сначала, что если модуль $P in bold(M)(A)$ рефлексивен (т. е.
  отображение $P arrow.r P^(**)$ является изоморфизмом) и если
  $T^(-1)P in PicCat(T^(-1)A)$, то $P in PicCat(A)$.
  #idx("рефлексивный модуль")

  Мы должны показать, что $P_(frak(m)) approx.eq A_(frak(m))$ для всех
  $frak(m) in maxSpec(A)$. Если $frak(m) inter T = emptyset$, то $P_(frak(m))$
  является локализацией кольца $T^(-1)P$, так что наше утверждение справедливо,
  поскольку $T^(-1)P in PicCat(T^(-1)A)$. Если $frak(m) inter T != emptyset$, то
  в силу предположения кольцо $A_(frak(m))$ факториально. Так как $T subset S$ и
  $Pic(S^(-1)A) = 0$, то $S^(-1)P = S^(-1)(T^(-1)P) approx.eq S^(-1)A$. Через
  $S_(frak(m))$ обозначим образ системы $S$ в $A_(frak(m))$. Так как система $S$
  состоит из неделителей нуля, то легко проверить, что $0 in.not S_(frak(m))$.
  Кроме того,
  $S_(frak(m))^(-1)P_(frak(m)) approx.eq (S^(-1)P)_(frak(m)) approx.eq
  (S^(-1)A)_(frak(m)) approx.eq S_(frak(m))^(-1)A_(frak(m))$. Поскольку мы имеем
  дело с конечно порожденными модулями над нётеровыми кольцами, функтор $Hom$
  перестановочен с локализацией. Таким образом, модуль $P_(frak(m))$
  рефлексивен. Поэтому
  $P_(frak(m)) subset S_(frak(m))^(-1)P_(frak(m)) approx.eq
  S_(frak(m))^(-1)A_(frak(m))$
  и модуль $P_(frak(m))$ изоморфен рефлексивному, а следовательно,
  дивизориальному дробному идеалу кольца $A_(frak(m))$. В силу предложения
  @prop:factorial-divisorial-ideal-principal $P_(frak(m)) approx.eq
  A_(frak(m))$.

  Для того чтобы показать, что отображение $Pic(A) arrow.r Pic(T^(-1)A)$
  сюръективно, предположим, что $Q in PicCat(T^(-1)A)$. Так как
  $Pic(S^(-1)A) = 0$, то $Q approx.eq frak(a)$ для некоторого идеала
  $frak(a) subset T^(-1)A$, такого, что $S^(-1)frak(a) = S^(-1)A$. Положим
  $frak(a)_0 = frak(a) inter A$. Тогда $frak(a)_0 inter S != emptyset$, и
  поэтому $frak(a)_0$ — невырожденный $A$-подмодуль в $S^(-1)A$ в смысле
  предложения @prop:fractional-submodule-hom-duality. Кроме того, из
  @prop:projective-base-change-rank следует, что идеал
  $frak(b) = (A\:(A\:frak(a)_0)) approx.eq frak(a)_0^(**)$ рефлексивен.
  Поскольку идеал $frak(a)$ обратим,
  $T^(-1)frak(b) approx.eq (T^(-1)frak(a)_0)^(**) = frak(a)^(**) approx.eq
  frak(a)$. Из последнего абзаца следует, что $frak(b) in PicCat(A)$ и
  $[Q] in Pic(T^(-1)A)$ является образом элемента $[frak(b)] in Pic(A)$.

  Предположим далее, что $frak(p) in M$, т. е. что $ht(frak(p)) = 1$ и
  $frak(p) inter T != emptyset$. Если $frak(m) inter T = emptyset$, то
  $frak(p)_(frak(m)) = A_(frak(m))$, а если $frak(m) inter T != emptyset$, то
  $frak(p)_(frak(m))$ либо совпадает с $A_(frak(m))$, либо является простым
  идеалом высоты $1$ в факториальном кольце. Таким образом, идеал $frak(p)$
  обратим и, следовательно, $frak(p) in Pic(A, T)$. Из предложения
  @prop:discrete-valuation-ring-characterizations следует, что $A_(frak(p))$ —
  кольцо дискретного нормирования. Таким #source(127) образом, можем определить
  «дивизорный гомоморфизм» $Div\: Pic(A, T) arrow.r Int^((M))$, полагая
  $Div(frak(a)) = sum_(frak(p)) v_(frak(p))(frak(a))frak(p)$ ($frak(p) in
  M$). Это отображение является гомоморфизмом частично упорядоченных групп, где
  если $frak(a) in Pic(A, T)$, то $frak(a) >= 0$ в том случае, когда
  $frak(a) subset A$. Как мы уже видели, это отображение сюръективно
  ($Div(frak(p)) = frak(p)$ для $frak(p) in M$). Достаточным условием для
  инъективности отображения (учитывая наличие порядка) является следующее: если
  $frak(a) in Pic(A, T)$ и $frak(a) subset A$, то
  $Div(frak(a)) = 0 => frak(a) = A$, т. е. $frak(a)_(frak(m)) = A_(frak(m))$ для
  всех $frak(m) in maxSpec A$. Это справедливо, если
  $frak(m) inter T = emptyset$, поскольку $frak(a) in Pic(A, T)$. В противном
  случае кольцо $A_(frak(m))$ факториально, и идеал $frak(a)_(frak(m))$ обратим
  в $A_(frak(m))$. Если $frak(p) in Ht_1(A)$ и $frak(a) subset frak(p)$, то
  $frak(p) inter T != emptyset$, и поэтому $frak(p) in M$. Таким образом,
  $frak(a)_(frak(m))$ не содержится в простых идеалах высоты $1$ в $A_(frak(m))$
  и, значит, в силу предложения @prop:factorial-divisorial-ideal-principal
  $frak(a)_(frak(m)) = A_(frak(m))$, что и требовалось доказать.
  #idx("дивизорный гомоморфизм")
]

#corollary[
  Пусть $R subset A$ — коммутативные нётеровы кольца и $T subset R$ —
  мультипликативная система неделителей нуля (в $A$), факториальная относительно
  $R$ и $A$. Пусть $M$ и $M'$ — множества простых идеалов высоты $1$ в $R$ и в
  $A$ соответственно, пересекающихся с $T$. Допустим, что если $frak(p) in M$,
  то $frak(p)' = frak(p)A$ — простой идеал и $frak(p)' inter R = frak(p)$. Тогда
  $frak(p)' in M'$ и получающееся отображение $M arrow.r M'$ биективно. Это
  отображение индуцирует изоморфизм $Pic(R, T) arrow.r Pic(A, T)$, при котором
  $frak(a) arrow.r.bar frak(a) A$.
] <cor:factorial-base-extension-relative-picard>
#proof[
  Если $frak(p) in M$, то в силу предложения
  @prop:factorial-localization-picard-surjection идеал $frak(p)$ обратим и,
  следовательно, $frak(p)' = frak(p)A$ — обратимый $A$-идеал. (Действительно,
  если $1 = sum_i frak(a)_i frak(b)_i$, где $frak(a)_i in frak(p)$ и
  $frak(b)_i frak(p) subset R$ для любого $i$, то $frak(b)_i frak(p)' subset A$
  также для любого $i$.) Следовательно, кольцо $A_(frak(p)')$ локальное с
  обратимым максимальным идеалом, и поэтому из
  @prop:discrete-valuation-ring-characterizations следует, что $A_(frak(p)')$ —
  кольцо дискретного нормирования. В частности, $ht(frak(p)') = 1$. Это
  показывает, что $frak(p)' in M'$. Обратно, если $frak(p)' in M'$, то
  $frak(p) = frak(p)' inter R$ — простой идеал, пересекающийся с $T$ и,
  следовательно, содержащий некоторый идеал $frak(p)_0 in M$. Так как
  $frak(p)_0 subset frak(p)$, то $frak(p)_0 A subset frak(p)A subset frak(p)'$.
  Поскольку $ht(frak(p)') = 1$, отсюда вытекает, что
  $frak(p)_0 A = frak(p)A = frak(p)'$, так как идеал $frak(p)_0 A$ простой.
  Следовательно,
  $frak(p) = frak(p)' inter R = frak(p)_0 A inter R = frak(p)_0 in M$. Таким
  образом, показано, что отображение $frak(p) arrow.r.bar frak(p)A$ из $M$ в
  $M'$ биективно.

  Если $frak(a) in Pic(R, T)$, то $frak(a) A in Pic(A, T)$, поскольку идеал
  $frak(a) A$ пересекается с $T$ и обратим над $A$ (см. начало приведенного выше
  доказательства). Получающееся отображение $Pic(R, T) arrow.r Pic(A, T)$
  является гомоморфизмом. В силу @prop:factorial-localization-picard-surjection
  эти группы являются свободными абелевыми группами с базисами $M$ и $M'$
  соответственно. Следовательно, из первой части доказательства вытекает, что
  указанный гомоморфизм является изоморфизмом.
]

#source(128) Заканчивая этот параграф, приведем без доказательства следующие
важные результаты:

#proposition[
  Пусть $A$ — кольцо Крулля и $t$ — переменная. Тогда $A[t]$ — кольцо Крулля и
  отображение $A arrow.r A[t]$ индуцирует изоморфизмы $C(A) arrow.r C(A[t])$ и
  $Pic(A) arrow.r Pic(A[t])$ (см. Бурбаки @bib:Bourbaki1971e, § 1, п. 9–10).
] <prop:krull-polynomial-class-group>

#theorem[
  Пусть $A$ — область целостности с полем частных $L$ и $A'$ — целое замыкание
  кольца $A$ в поле $L'$, представляющем собой конечное расширение поля $L$.
  Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[если $A$ — конечно порожденная алгебра
      над полем, то $A'$ — конечномерная $A$-алгебра, т. е. $A' in bold(M)(A)$
      (см. Бурбаки @bib:Bourbaki1971c, § 3, п.
      2);] <cond:integral-closure-finite-type-finite>

    #condition-item(format: "cyrillic")[пусть $A$ — кольцо Крулля. Тогда $A'$
      является кольцом Крулля. Кроме того, если поле $L'$ сепарабельно над $L$,
      то $A'$ содержится в некотором конечно порожденном $A$-модуле в $L'$ (см.
      Бурбаки @bib:Bourbaki1971e, § 1, п. 8 и @bib:Bourbaki1971c, § 1, п. 7, а
      также теорему @th:maximal-orders-existence настоящей
      главы).] <cond:integral-closure-krull-separable-lattice>
  ]
] <th:integral-closure-finite-field-extension>
#name-idx("Бурбаки (Bourbaki N.)")

#theorem[
  Пусть $A$ — коммутативное нётерово кольцо и $S$ — мультипликативная система,
  регулярная относительно $A$ (см. § @sec:homological-dimension). Тогда система
  $S$ факториальна относительно $A$.
] <th:regular-system-factorial>
В силу предложения @prop:finite-algebra-global-dimension-regularity мы знаем,
что если $frak(m) in maxSpec(A)$ и $frak(m) inter S != emptyset$, то кольцо
$A_(frak(m))$ регулярно. В теореме утверждается, что кольцо $A_(frak(m))$ должно
также быть факториальным. Таким образом, нам хотелось бы знать, что регулярное
локальное кольцо факториально. Но это хорошо известная теорема Ауслендера —
Буксбаума @bib:Auslander1959.
