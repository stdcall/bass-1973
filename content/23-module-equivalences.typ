#import "main-defs.typ": (
  Aut, End, Hom, Id, Im, Ker, ann, idx, moduleCategory, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, definition, lemma, proof, proposition,
  theorem,
)
#import "diagrams/module-categories-diagrams.typ": (
  map-arrow, module-equivalence, morita-square-p, morita-square-q,
  split-projective,
)

== Эквивалентности категорий модулей <sec:module-equivalences>

Пусть $R$~— фиксированное коммутативное кольцо, и пусть все наши кольца $A$,
$B$, … являются $R$-алгебрами. Тот факт, что $M$ является левым
$A tensor_R B^degree$-модулем, иногда будет обозначаться так:
$attach(M, bl: A, br: B)$ (следуя соглашению Картана~— Эйленберга).
#idx("соглашение Картана — Эйленберга")

Этот параграф содержит детальный анализ эквивалентностей из
$moduleCategory hyph A$ в $moduleCategory hyph B$. Соберем воедино ряд следствий
теоремы @th:eilenberg-watts.

#proposition[
  Пусть $A$ и $B$~— две $R$-алгебры, и пусть
  $ #module-equivalence() $
  — $R$-функторы, такие, что $S T tilde.eq Id_(moduleCategory hyph A)$ и
  $T S tilde.eq Id_(moduleCategory hyph B)$. Положим $P = T A$ и $Q = S B$.
  Тогда мы находимся в ситуации
  $(attach(P, bl: A, br: B), attach(Q, bl: B, br: A))$ и

  #condition-list[
    #condition-item[$T tilde.eq tensor_A P$ и
      $S tilde.eq tensor_B Q$;] <cond:equivalence-tensor-functors>

    #condition-item[существуют изоморфизмы бимодулей
      $
        f: P tensor_B Q -> A quad "и" quad g: Q tensor_A P -> B;
      $] <cond:equivalence-pairings>

    #condition-item[#source(64) можно выбрать изоморфизмы $f$ и $g$ так, что
      диаграммы
      $ #morita-square-p() $
      и
      $ #morita-square-q() $
      коммутативны. (В этих диаграммах отображения $alpha$ и $beta$
      стандартные.)] <cond:equivalence-associative-pairings>
  ]
] <prop:equivalence-morita-context>

#proof[
  Все, кроме утверждения @cond:equivalence-associative-pairings, следует
  непосредственно из теоремы @th:eilenberg-watts и замечания о том, что
  эквивалентность непрерывна справа. Для доказательства п.
  @cond:equivalence-associative-pairings предположим, что мы хотели бы добиться
  коммутативности первой диаграммы. Поскольку все отображения являются
  изоморфизмами бимодулей, то по крайней мере
  $beta(1 tensor g) = u alpha(f tensor 1)$ для некоторого
  $u in Aut_(A hyph B)(P)$. В частности,
  $u in Hom_B (P, P) = Hom_B (T A, T A) tilde.eq Hom_A (A, A) = A$, и поэтому
  $u$ является умножением слева на элемент из $A$, который мы отождествим с $u$.
  Так как $u$ также является $A$-гомоморфизмом, то $u$ лежит в центре кольца
  $A$. Теперь очевидно, что $u alpha = alpha(u tensor 1_P)$, и поэтому если
  заменить $f$ на $u f$, то первый квадрат будет коммутативным. В этом случае мы
  покажем, что второй квадрат тоже оказывается коммутативным. Для того чтобы
  избежать повторения этого рассуждения, в дальнейшем мы прервем доказательство
  и дадим определение, подсказанное этим предложением.
]

#definition[
  _Ситуация предэквивалентности_#idx("ситуация предэквивалентности")
  $(A, B, P, Q, f, g)$ состоит из $R$-алгебр $A$ и $B$, бимодулей
  $attach(P, bl: A, br: B)$ и $attach(Q, bl: B, br: A)$ и гомоморфизмов
  бимодулей $f: P tensor_B Q -> A$ и $g: Q tensor_A P -> B$, которые
  «ассоциативны» в следующем смысле:

  #condition-list[
    #condition-item[$(p q) p' = p(q p')$,] <cond:morita-p-associativity>

    #condition-item[$(q p) q' = q(p q')$ (для всех $p, p' in P$;
      $q, q' in Q$),] <cond:morita-q-associativity>
  ]

  где мы обозначаем $f(p tensor q) = p q$ и $g(q tensor p) = q p$. Если $f$ и
  $g$~— изоморфизмы, то будем говорить, что нам дана _ситуация
  эквивалентности_.#idx("ситуация эквивалентности")
] <def:morita-context>

Теперь доказательство предложения @prop:equivalence-morita-context завершается
следующей леммой:

#source(65)
#lemma[
  Условие @cond:morita-q-associativity в определении ситуации
  предэквивалентности вытекает из других условий, если из того, что $d in Q$ и
  $d p' = 0$ для всех $p' in P$, следует, что $d = 0$. Последнее условие
  выполняется, если $g$ инъективно и функтор $tensor_A P$ строгий.
] <lem:morita-context-associativity>

#proof[
  Если $q, q' in Q$ и $p in P$, то нам надо показать, что $(q p) q' = q(p q')$.
  Для любого элемента $p' in P$:
  $
    ((q p) q') p' & = (q p)(q' p') && quad (g " " B "-линейно слева") \
    & = q(p(q' p')) && quad (g " " B "-линейно справа") \
    & = q((p q') p') && quad (#[условие @cond:morita-p-associativity]) \
    & = (q(p q')) p' && quad (g " " A "-билинейно").
  $
  Следовательно, если $d = (q p) q' - q(p q')$, то $d p' = 0$ для всех $p' in P$
  и поэтому в силу предположения $d = 0$.

  Для доказательства последнего утверждения рассмотрим $h: A -> Q$, где
  $h(a) = d a$. Тогда применение инъективного отображения $g$ после гомоморфизма
  $h tensor 1_P: A tensor_A P -> Q tensor_A P$ отображает все в нуль и,
  следовательно, $h tensor 1_P = 0$. Таким образом, если функтор $tensor_A P$
  строгий, то $h = 0$.
]

#theorem[
  Пусть $(A, B, P, Q, f, g)$~— ситуация предэквивалентности. Допустим, что
  отображение $f$ сюръективно. Тогда

  #condition-list[
    #condition-item[$f$~—
      изоморфизм;] <cond:surjective-morita-pairing-isomorphism>

    #condition-item[$P$ и $Q$ являются образующими в категории
      $A$-модулей;] <cond:surjective-morita-generators>

    #condition-item[$B$-модули $P$ и $Q$ конечно порождены и
      проективны;] <cond:surjective-morita-projective>

    #condition-item[отображение $g$ индуцирует изоморфизмы бимодулей
      $P tilde.eq Hom_B (Q, B)$ и
      $Q tilde.eq Hom_B (P, B)$;] <cond:surjective-morita-duals>

    #condition-item[гомоморфизмы $R$-алгебр
      $
        End_B (P) <- A -> End_B (Q)^degree,
      $
      индуцированные структурой бимодулей, являются
      изоморфизмами.] <cond:surjective-morita-endomorphisms>
  ]
] <th:surjective-morita-context>

#proof[
  Предположение об отображении $f$ означает, что можно записать
  $
    1 = sum_(i in I) p_i q_i quad "в" quad A.
  $ <eq:morita-surjectivity-unit>

  @cond:surjective-morita-pairing-isomorphism Пусть
  $sum p'_j tensor q'_j in Ker f$. Тогда, используя
  @eq:morita-surjectivity-unit, убеждаемся, что
  $
    sum_j p'_j tensor q'_j & = sum_(i, j)(p'_j tensor q'_j) p_i q_i
                             = sum_(j, i) p'_j tensor ((q'_j p_i) q_i) \
                           & = sum_(i, j)(p'_j (q'_j p_i)) tensor q_i
                             = sum_(i, j)(p'_j q'_j)(p_i tensor q_i) \
                           & = (sum_j p'_j q'_j)(sum_i p_i tensor q_i) = 0,
  $
  так как $sum_j p'_j q'_j = 0$.

  @cond:surjective-morita-generators Линейные функционалы $h_i: P -> A$, где
  $h_i (p) = p(q_i)$, определяют гомоморфизм $h: P^((I)) -> A$. Из условия
  @eq:morita-surjectivity-unit следует, что отображение $h$ сюръективно, поэтому
  модуль $P$ является образующим в $A hyph moduleCategory$. Аналогичные
  рассуждения применимы к $Q$.

  #source(66) @cond:surjective-morita-projective Определим
  $#split-projective()$, полагая $e(p) = (q_i p)$ и $h(b_i) = sum p_i b_i$.
  Тогда $h e(p) = sum p_i (q_i p) = (sum p_i q_i) p = p$. Таким образом, $P$~—
  конечно порожденный и проективный $B$-модуль. Аналогичное рассуждение
  применимо к $Q$.

  @cond:surjective-morita-duals Отображение $g$ индуцирует гомоморфизм бимодулей
  $h: P -> Hom_B (Q, B)$, где $h(p)(q) = q p$. Если $h(p) = 0$, то
  $p = sum(p_i q_i) p = sum p_i (q_i p) = 0$, и поэтому отображение $h$
  инъективно. Для доказательства сюръективности рассмотрим $f: Q -> B$. Тогда
  $
    f(q) & = f(sum q(p_i q_i)) = f(sum(q p_i) q_i)
           = sum(q p_i) f(q_i) \
         & = sum q(p_i f(q_i)) = h(p)(q),
  $
  где $p = sum p_i f(q_i)$. Аналогично $Q tilde.eq Hom_B (P, B)$.

  @cond:surjective-morita-endomorphisms Мы должны показать, что
  $h: A -> End_B (P)$, где $h(a)(p) = a p$, является изоморфизмом. Если
  $h(a) = 0$, то $a = sum a(p_i q_i) = sum(a p_i) q_i = 0$, поэтому отображение
  $h$ инъективно. Пусть теперь $f: P -> P$. Тогда
  $
    f(p) & = f(sum(p_i q_i) p) = f(sum p_i (q_i p)) \
         & = sum f(p_i)(q_i p) = sum(f(p_i) q_i) p = h(a) p,
  $
  где $a = sum f(p_i) q_i$, т. е. отображение $h$ сюръективно. Аналогично
  показывается, что $A -> End_B (Q)^degree$~— изоморфизм.
]

#theorem[
  Пусть $(A, B, P, Q, f, g)$~— ситуация эквивалентности (см. определение
  @def:morita-context). Тогда

  #condition-list[
    #condition-item[$P$ и $Q$~— обратимые бимодули (см.
      @cor:invertible-bimodule).] <cond:morita-invertible-bimodules>

    #condition-item[$P$ и $Q$~— строго проективны и как $A$-модули, и как
      $B$-модули.] <cond:morita-strict-projectivity>

    #condition-item[Отображения $f$ и $g$ индуцируют изоморфизмы каждого из
      бимодулей $P$ и $Q$ с дуальными модулями к другому относительно $A$ и
      $B$.] <cond:morita-duals>

    #condition-item[Гомоморфизмы $R$-алгебр
      $
        End_B (P) <- A -> End_B (Q)^degree
      $
      и
      $
        End_A (P)^degree <- B -> End_A (Q),
      $
      индуцированные структурой бимодуля на $P$ и $Q$, являются
      изоморфизмами.] <cond:morita-endomorphism-rings>

    #condition-item[Кольца эндоморфизмов бимодулей $A$, $B$, $P$ и $Q$
      (канонически) изоморфны центрам колец $A$, $B$ и центрам категорий
      $moduleCategory hyph A$, $moduleCategory hyph B$ (см. предложение
      @prop:center-module-category).] <cond:morita-centers>

    #condition-item[Структура правых $A$-идеалов изоморфна (при соответствии
      $frak(a) arrow.r.bar frak(a) P$) структуре $B$-подмодулей бимодуля $P$,
      двусторонние идеалы переходят в $A$-$B$-подмодули или, что эквивалентно,
      во вполне #source(67)инвариантные $B$-подмодули. Аналогичные утверждения
      имеют место с соответствующими перестановками внутри пар (левый, правый),
      $(A, B)$ и $(P, Q)$. В частности, из соображений симметрии следует, что
      структуры двусторонних идеалов колец $A$ и $B$
      изоморфны.] <cond:morita-submodule-lattices>

    #condition-item[Функтор $T = Hom_A (P, dot) tilde.eq Q tensor_A dot:
      A hyph moduleCategory -> B hyph moduleCategory$ является эквивалентностью
      категорий. Если $M in A hyph moduleCategory$, то модуль $M$ конечно
      порожден (над $A$) тогда и только тогда, когда модуль $T M$ конечно
      порожден (над $B$). Кроме того, при структурном изоморфизме из п.
      @cond:morita-submodule-lattices двусторонние идеалы $ann_A (M)$ в кольце
      $A$ соответствуют двусторонним идеалам $ann_B (T M)$ в кольце $B$. В
      частности, [модуль $M$ точен (над $A$)] $<=>$ [модуль $T M$ точен (над
      $B$)].] <cond:morita-left-module-equivalence>
  ]
] <th:morita-equivalence-properties>

#proof[
  Утверждение @cond:morita-invertible-bimodules следует непосредственно из
  предположения и определения @cor:invertible-bimodule.

  Утверждения @cond:morita-strict-projectivity–@cond:morita-endomorphism-rings
  следуют немедленно из
  @cond:surjective-morita-generators–@cond:surjective-morita-endomorphisms
  теоремы @th:surjective-morita-context.

  Утверждение @cond:morita-centers следует из рассмотрения изоморфизмов центр
  кольца $A = End_(A hyph A)(A) #map-arrow($tensor_A P$) End_(A hyph B)(P)$,
  центр кольца
  $B = End_(B hyph B)(B) #map-arrow($P tensor_B$) End_(A hyph B)(P)$,
  аналогичных изоморфизмов для модуля $Q$ и из предложения
  @prop:center-module-category.

  Докажем теперь @cond:morita-submodule-lattices. Так как модуль $P$ проективен,
  то для правого $A$-идеала $frak(a)$ каноническое отображение
  $frak(a) tensor_A P -> frak(a) P$ является изоморфизмом. Таким образом,
  утверждение о том, что отображение $frak(a) arrow.r.bar frak(a) P$ является
  изоморфизмом структуры правых $A$-подмодулей модуля $A$ в структуру
  $B$-подмодулей модуля $P = A tensor_A P$, следует из того, что функтор
  $tensor_A P$ является эквивалентностью. Кроме того, так как
  $A = End_(moduleCategory hyph A)(A) = End_B (P)$, то вполне инвариантные
  подмодули в $A$ и $P$ являются соответственно двусторонними идеалами и
  $A$-$B$-подмодулями. Очевидно, что они соответствуют друг другу при
  эквивалентности.

  Оставшиеся утверждения из п. @cond:morita-submodule-lattices очевидны.
  Изоморфизм структур двусторонних идеалов в $A$ и $B$ переводит
  $frak(a) subset A$ в $frak(b) subset B$ тогда и только тогда, когда
  $frak(a) P = P frak(b)$. Приведенные выше рассуждения показывают, что это
  действительно биективное отображение.

  Наконец, докажем п. @cond:morita-left-module-equivalence. Если
  $M, N in A hyph moduleCategory$, то обозначим $N^* = Hom_A (N, A)$ и определим
  отображение $h_N: N^* tensor_A M -> Hom_A (N, M)$, полагая
  $h_N (f tensor x)(n) = f(n) x$. Очевидно, что это естественное преобразование
  и отображение $h_A$~— изоморфизм. Следовательно, в силу аддитивности
  отображение $h_N$ является изоморфизмом для любого конечно порожденного
  проективного модуля $N$. В силу утверждения @cond:morita-strict-projectivity и
  @cond:morita-duals, таким образом, функторы $T = Hom_A (P, dot)$ и
  $Q tensor_A$ изоморфны. Если модуль $M in A hyph moduleCategory$ конечно
  порожден, то $Q tensor_A M$ является конечно порожденным $B$-модулем
  (поскольку $Q$ конечно порожден). Обратно, если модуль #source(68)$T M$
  конечно порожден, то модуль $M$ конечно порожден, поскольку $T$~—
  эквивалентность.

  Пусть $frak(a) = ann_A (M)$. Тогда $frak(a) P$ можно охарактеризовать как
  наибольший подмодуль в $P$, переходящий в нуль при любом $A$-гомоморфизме
  $P -> M$. Следовательно, $frak(b) = T(frak(a) P)$~— наибольший подмодуль в
  $B = T(P)$, аннулирующий каждый $B$-гомоморфизм $B -> T M$, т. е.
  $frak(b) = ann_B (T M)$. Из п. @cond:morita-submodule-lattices мы знаем, что
  идеал $frak(c)$ в $B$, соответствующий идеалу $frak(a)$, характеризуется
  равенством $frak(a) P = P frak(c)$. Следовательно,
  $T(frak(a) P) = Hom(P, P frak(c)) = B frak(c) = frak(c)$, и поэтому
  $frak(c) = frak(b)$. Теорема доказана.
]
