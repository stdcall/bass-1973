#import "main-defs.typ": (
  End, GL, Hom, Im, Ker, U, idx, moduleCategory, projLim, rad, source,
  symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition,
  variant-condition,
)
#import "diagrams/rings-modules-diagrams.typ": projective-reduction-square

== Радикал Джекобсона и идемпотенты <sec:jacobson-radical-idempotents>

Если $A$~— кольцо и $M in moduleCategory hyph A$, то положим
$rad M = inter.big Ker(h)$ ($h: M -> S$; $S$~— простой модуль). Предположим, что
$g: N -> M$. Тогда $h g: N -> S$, и поэтому $h g (rad N) = 0$ для всех $h$.
Таким образом, $g(rad N) subset rad M$, и поэтому $rad$ является подфунктором
тождественного функтора. В частности, $rad M$~— вполне инвариантный подмодуль
модуля $M$. Применяя это замечание к левым умножениям в кольце $A$, убеждаемся,
что $rad A$ _является двусторонним идеалом_. Если $J$~— двусторонний идеал и
$J subset rad A$, то $J$ содержится в каждом максимальном правом идеале кольца
$A$ и поэтому, как легко видеть, $rad (A slash J) = (rad A) slash J$. В
частности,
$
  rad (A slash (rad A)) = 0.
$
#symbol-idx($rad$, sort: "rad", group: "operators", order: 67)
Если $S$~— простой правый $A$-модуль и $x in S$, то определим $f: A -> S$,
полагая $f(a) = x a$. Тогда $f(rad A) = 0$. Поэтому в силу произвольности выбора
элемента $x$ имеем $S dot rad A = 0$. Если $h: M -> S$~— гомоморфизм, то
$h(M dot rad A) subset S dot rad A = 0$. Итак,
$
  M dot rad A subset rad M
$
для любого модуля $M in moduleCategory hyph A$.

#proposition[
  Пусть $N$~— подмодуль в $M in bold(M)(A)$. Следующие условия эквивалентны:

  #condition-list[
    #condition-item[$N subset rad M$.] <cond:submodule-in-radical>
    #condition-item[Если $H$~— подмодуль в $M$, то из $N + H = M$ следует, что
      $H = M$.] <cond:submodule-superfluous>
  ]
] <prop:radical-superfluous-submodules>

#proof[
  $#[@cond:submodule-in-radical] => #[@cond:submodule-superfluous]$.
  Предположим, что $H != M$. Так как модуль $M$ конечно порожден, то, применяя
  лемму Цорна, #source(81)найдем максимальный собственный подмодуль $L$,
  содержащий $H$. Так как $N subset rad M$, то $N subset L$ и потому
  $N + H subset L$. Противоречие.

  Обратно, из условия $#[@cond:submodule-superfluous]$ очевидным образом
  вытекает, что $N$ содержится в любом максимальном собственном подмодуле, и,
  следовательно, в их пересечении, которое является радикалом модуля $M$.
]

#proposition(title: [«лемма Накаямы»])[
  Следующие условия на правый идеал $J$ кольца $A$ эквивалентны:

  #condition-list[
    #condition-item[$J subset rad A$;] <cond:nakayama-ideal-in-radical>
    #condition-item[если $M in bold(M)(A)$, то $M J = M => M = 0$;]
    <cond:nakayama-quotient-vanishing>
    #variant-condition[если $M in bold(M)(A)$ и $H$~— подмодуль в $M$, то
      $M = H + M J => M = H$;] <cond:nakayama-submodule-equality>
    #condition-item[множество $1 + J$ состоит из обратимых элементов (и поэтому
      $1 + J$ является подгруппой в группе $U(A)$).]
    <cond:nakayama-unit-coset>
  ]
] <prop:nakayama-lemma>
#idx("лемма", "Накаямы")

#proof[
  Так как $M(rad A) subset rad M$ для всех $M$, то из предложения
  @prop:radical-superfluous-submodules следует, что
  $#[@cond:nakayama-ideal-in-radical] => #[@cond:nakayama-submodule-equality]$
  и, в частности, когда $M = A$, что
  $#[@cond:nakayama-submodule-equality] => #[@cond:nakayama-ideal-in-radical]$.
  Очевидно, что $#[@cond:nakayama-submodule-equality] =>
  #[@cond:nakayama-quotient-vanishing]$. Обратно, условие
  $#[@cond:nakayama-submodule-equality]$ вытекает из
  $#[@cond:nakayama-quotient-vanishing]$, если
  $#[@cond:nakayama-quotient-vanishing]$ применить к $M slash H$.

  $#[@cond:nakayama-submodule-equality] => #[@cond:nakayama-unit-coset]$. Если
  $x in J$, то положим $u = 1 + x$. Тогда $A = J + u A$, и поэтому $A = u A$.
  Выберем элемент $v$ так, чтобы $u v = 1$. Так как $1 = u v = v + x v$, то
  $v = 1 - x v in 1 + J$, и потому элемент $v$ обладает правым обратным. Таким
  образом, $u$~— обратимый элемент, и $v = u^(-1) in 1 + J$.

  $#[@cond:nakayama-unit-coset] => #[@cond:nakayama-ideal-in-radical]$.
  Утверждаем, что $J$ содержится в каждом максимальном правом идеале $H$. Если
  это не так, то $J + H = A$ и $1 = x + y$, где $x in J$, $y in H$. Тогда в силу
  условия $#[@cond:nakayama-unit-coset]$ элемент $y = 1 - x$ обратим, значит,
  $H = A$. Противоречие.
]

#corollary[
  Пересечение максимальных левых идеалов совпадает с $rad A$.
] <cor:jacobson-radical-left-right>

#proof[
  Обозначим через $J$ это пересечение. Так как $rad A$ является двусторонним
  идеалом и $1 + rad A subset U(A)$, то в силу левостороннего аналога
  предложения~@prop:nakayama-lemma $rad A subset J$. Симметрично
  $J subset rad A$.
]

#corollary[
  Каждый ниль-идеал (т. е. идеал, в котором каждый элемент нильпотентен) лежит в
  $rad A$.
] <cor:nil-ideal-in-radical>

#proof[
  Если $x^n = 0$, то
  $
    (1 - x)^(-1) = 1 + x + dots + x^(n-1).
  $
]

#corollary[
  Пусть $R$~— коммутативное кольцо и $A$~— конечномерная $R$-алгебра. Тогда
  $A(rad R) subset rad A$.
] <cor:finite-algebra-base-radical>

#proof[
  #source(82)Предположим, что $M in bold(M)(A)$ и $M dot (rad R) = M$. Так как
  $M in bold(M)(R)$, то из условия @cond:nakayama-quotient-vanishing предложения
  @prop:nakayama-lemma следует, что $M = 0$ и, следовательно,
  $A(rad R) subset rad A$.
]

#proposition[
  Пусть $P$~— строго проективный правый $A$-модуль. Тогда
  $rad P = P dot (rad A)$ и $rad (End_A (P)) = Hom_A (P, rad P)$. В частности,
  $rad M_n (A) = M_n (rad A)$.
] <prop:radical-morita-invariance>

#proof[
  Отображения $M arrow.r.bar rad M$ и $M arrow.r.bar M dot (rad A)$ являются
  аддитивными функторами, совпадающими на $M = A$ и, следовательно, на всех
  $P in bold(P)(A)$. Если модуль $P$ строго проективен и $B = End_A (P)$, то
  функтор $h(M) = Hom_A (P, M)$ является эквивалентностью из категории
  $moduleCategory hyph A$ в $moduleCategory hyph B$. В частности,
  $h(rad M) = rad h(M)$, что и требовалось доказать.
]

#corollary[
  Если $J$~— двусторонний идеал, лежащий в $rad A$, то отображение
  $GL_n (A) -> GL_n (A slash J)$ сюръективно при всех $n >= 1$.
] <cor:general-linear-radical-surjection>

#proof[
  Если элемент $u in A$ отображается в $U(A slash J)$, то можно разрешить
  сравнение $u v equiv v u equiv 1 mod J$ в $A$. Тогда
  $u v, v u in 1 + J subset U(A)$ и, следовательно, $u in U(A)$. Таким образом,
  отображение $U(A) -> U(A slash J)$ сюръективно. Применим это рассуждение к
  отображению $M_n (A) -> M_n (A slash J) = M_n (A) slash M_n (J)$, используя
  то, что $M_n (J) subset rad M_n (A)$ (см.
  предложение~@prop:radical-morita-invariance).
]

_Замечание._ Из этого доказательства ясно, что $GL_n (A)$ является полным
прообразом в $M_n (A)$ группы $GL_n (A slash J)$.

Назовем кольцо $A$ _полулокальным_, если кольцо $A slash (rad A)$ полупросто.
Так как радикал кольца $A slash (rad A)$ равен нулю, то в нем нет ненулевых
нильпотентных идеалов. Следовательно, из теоремы
@th:semisimple-ring-characterizations вытекает, что кольцо $A$ полулокально, как
только кольцо $A slash (rad A)$ артиново справа. Кроме того, в этом случае оно
является произведением конечного числа колец матриц над телами. Из
предложения~@prop:radical-morita-invariance вытекает, что если кольцо $A$
полулокально, то и кольцо $M_n (A)$ полулокально. Назовем кольцо $A$
_локальным_, если $A slash (rad A)$~— тело. Заметим, что это условие
эквивалентно определению из (гл.~@ch:category-algebra,
§~@sec:additive-categories). Если $A$~— локальное кольцо, то
$A = U(A) union rad A$. #idx(
  "кольцо",
  "полулокальное",
)#idx("полулокальное кольцо") #idx("кольцо", "локальное")#idx(
  "локальное кольцо",
)

Следующее предложение будет часто использоваться в
гл.~@ch:stable-projective-structure и @ch:stable-linear-groups.

#proposition[
  Пусть $frak(a)$~— правый идеал в полулокальном кольце $A$. Пусть элемент
  $b in A$ таков, что $frak(a) + b A = A$. Тогда в $frak(a) + b$ содержится
  обратимый элемент кольца $A$.
] <prop:semilocal-unit-in-coset>

#proof[
  #source(83)Элемент кольца $A$ обратим тогда и только тогда, когда он обратим
  по модулю $rad A$ (см. приведенное выше замечание). Следовательно, переходя к
  $A slash (rad A)$, можно считать, что $rad A = 0$. Тогда кольцо $A$ разложимо
  в произведение колец, и достаточно доказать наше утверждение для каждого из
  сомножителей. Значит, можем далее считать, что $A = End_D (V)$, где $V$~—
  конечномерное правое векторное пространство над телом $D$. В этом случае
  $frak(a)$ является множеством всех $a: V -> V$, таких, что
  $a V subset W = frak(a) V$ (см., например, теорему
  @th:morita-equivalence-properties@cond:morita-submodule-lattices). Так как
  $frak(a) + b A = A$, то $W + Im(b) = V$. Выберем $W_0 subset W$ так, чтобы
  $V = W_0 plus.o Im(b)$. Если $V = Ker(b) plus.o U$, то $b$ индуцирует
  изоморфизм пространства $U$ на $Im(b)$, и поэтому $Ker(b) tilde.eq W_0$.
  Выберем $a$ так, что $a U = 0$ и $a$ индуцирует изоморфизм из $Ker(b)$ на
  $W_0$. Тогда $a V = W_0 subset W$, поэтому $a in frak(a)$. Кроме того, $a + b$
  является, очевидно, автоморфизмом пространства $V$.
]

#corollary[
  Пусть $frak(q)$~— двусторонний идеал в полулокальном кольце $A$. Тогда
  отображение $GL_n (A) -> GL_n (A slash frak(q))$ сюръективно при всех
  $n >= 1$.
] <cor:general-linear-semilocal-surjection>

#proof[
  Если элемент $u in A$ обратим по модулю $frak(q)$, то $frak(q) + u A = A$, и
  поэтому в $frak(q) + u$ содержится обратимый элемент кольца $A$. Итак,
  отображение $U(A) -> U(A slash frak(q))$ сюръективно. Следствие вытекает из
  применения этого замечания к кольцу $M_n (A)$, которое также полулокально.
]

Далее мы обсудим проблему поднятия идемпотентов.

#proposition[
  Пусть $J$~— двусторонний идеал в кольце $A$. Допустим, что либо $J$~—
  ниль-идеал, либо кольцо $A$ $J$-адически полно (т. е. отображение
  $A -> projLim A slash J^n$~— изоморфизм). В этом случае конечное множество
  ортогональных идемпотентов может быть поднято по модулю идеала $J$, т. е. если
  $a_1, dots, a_m in A$ и $a_i a_j equiv delta_(i j) a_i mod J$ при
  $1 <= i, j <= m$, то существуют элементы $e_1, dots, e_m in A$, для которых
  $e_i equiv a_i mod J$ и $e_i e_j = delta_(i j) e_i$ при $1 <= i, j <= m$.
] <prop:orthogonal-idempotent-lifting>

#proof[
  Пусть $a in A$. Для любого $n > 0$
  $
    1 = (a + (1 - a))^(2n) =
    sum_(0 <= j <= 2n) binom(2n, j) a^(2n-j) (1 - a)^j.
  $
  Положим $f_n (a) = sum_(0 <= j <= n) binom(2n, j) a^(2n-j) (1-a)^j =
  1 - sum_(n < j <= 2n) binom(2n, j) a^(2n-j) (1-a)^j$. Заметим, что $f_n$~—
  многочлен от $a$ с целыми коэффициентами и, следовательно, принадлежит кольцу
  $R$, порожденному элементом $a$, при этом
  $
    f_n (a) equiv 0 mod a^n R; \
    f_n (a) equiv 1 mod (1 - a)^n R.
  $
  #source(84)Отсюда следует, что $f_n (a)^2 equiv f_n (a) mod (a(1-a))^n R$. Так
  как $a^n R + (1-a)^n R = R$, то $(a(1-a))^n R = a^n R inter (1-a)^n R$ (см.
  предложение @prop:chinese-remainder-modules ниже). Поэтому
  $f_n (a) equiv f_(n-1) (a) mod (a(1-a))^(n-1) R$.

  Для $n = 1$ получаем $f_1 (a) = binom(2, 0) a^2 + binom(2, 1) a(1-a) =
  a^2 + 2a(1-a) = 2a - a^2 = a + a(1-a) equiv a mod a(1-a) R$. Таким образом,
  $f_n (a) equiv a mod a(1-a) R$.

  Пусть теперь $a^2 - a = a(a - 1)$~— нильпотентный элемент. Тогда при
  достаточно большом $n$ получим $f_n (a) equiv a mod (a^2 - a) R$ и
  $f_n (a)^2 = f_n (a)$. Это показывает возможность поднимать идемпотенты по
  модулю ниль-идеала $J$ (поскольку в этом случае $a^2 - a in J$). Если, с
  другой стороны, кольцо $A$ $J$-адически полно, то мы можем по индукции
  построить $e_n in A$, для которых $e_1 = a$, $e_n^2 equiv e_n mod J^n$ и
  $e_(n+1) equiv e_n mod J^n$ (поскольку $J slash J^n$~— нильпотентный идеал, мы
  можем применить нашу конструкцию). Последовательность $e_n$ сходится к
  $e in A = projLim A slash J^n$. При этом $e equiv a mod J$ и $e^2 = e$. Это
  доказывает предложение в случае одного идемпотента.

  В общем случае предположим, что требуемые идемпотенты $e_1, dots, e_(m-1)$ уже
  построены, тогда $e = e_1 + dots + e_(m-1)$~— идемпотент, при этом
  $e equiv a_1 + dots + a_(m-1) mod J$. Следовательно, $e$ и $a_m$~—
  ортогональные идемпотенты по $mod J$. Пусть $f = 1 - e$, $b = f a_m f$. Тогда
  очевидно, что $b equiv a_m mod J$ и $e b = 0 = b e$. Образуем, как и раньше,
  последовательность $f_n (b)$, сходящуюся к идемпотенту $e_m$ и такую, что
  $e_m equiv b mod J$. Так как $f_n (b)$~— многочлен от $b$ с целыми
  коэффициентами и нулевым свободным членом, то $e f_n (b) = 0 = f_n (b) e$.
  Следовательно, $e$ и $e_m$ ортогональны. Если $i < m$, то
  $e_i e = e_i = e e_i$, откуда следует, что $e_m$ и $e_i$ ортогональны.
]

#proposition[
  Пусть $A$~— артиново справа кольцо и $J = rad A$. Каждый ненильпотентный
  правый идеал кольца $A$ содержит ненулевой идемпотент, в частности, $J$~—
  нильпотентный идеал. Более того, кольцо $A slash J$ полупросто.
] <prop:artinian-ring-radical-nilpotent>

#proof[
  Так как в $A slash J$ нет ненулевых нильпотентных идеалов, то полупростота
  кольца $A slash J$ следует из теоремы @th:semisimple-ring-characterizations.

  Если $e in J$~— идемпотент, то $e A = (e A)^2$. В силу леммы Накаямы
  $e A = 0$. Таким образом, из первого утверждения следует, что $J$~—
  нильпотентный идеал.

  Предположим, что первое утверждение не имеет места, и пусть $I$~— минимальный
  правый ненильпотентный идеал, не содержащий ненулевого идемпотента. Так как
  $I^2 subset I$ также не является нильпотентным идеалом, то $I^2 = I$. Пусть
  $H$~— минимальный среди правых идеалов кольца $A$, таких, что $H I != 0$
  (например, сам идеал $I$). Выберем $x in H$ так, чтобы $x I != 0$. Из
  минимальности #source(85)следует, что $x I = H$. Пусть элемент $a in I$ таков,
  что $x a = x$. Тогда $x a^2 = x a$, поэтому
  $a^2 - a in N = {y in I | x y = 0}$. Так как $N subset I$, то минимальность
  идеала $I$ влечет за собой нильпотентность идеала $N$, и, следовательно,
  $a^2 - a$~— нильпотентный элемент. Пусть $R$~— подкольцо, порожденное
  элементом $a$. По предложению @prop:orthogonal-idempotent-lifting существует
  идемпотент $e in R$, для которого $e equiv a mod (a^2 - a) R$. В частности,
  $e equiv a mod N$. Так как $a in I$, $a in.not N$, то $e in I$, $e in.not N$,
  что заканчивает доказательство.
]

#proposition[
  Пусть $J$~— двусторонний идеал, лежащий в $rad A$. Положим
  $overline(A) = A slash J$ и $overline(M) = M tensor_A overline(A) =
  M slash (M J)$, где $M in moduleCategory hyph A$. Тогда
  $
    overline(dot): bold(P)(A) -> bold(P)(overline(A))
  $
  ~— полный аддитивный функтор, обладающий следующими свойствами:

  #condition-list[
    #condition-item(format: "cyrillic")[если $f: P -> Q$~— морфизм в
      $bold(P)(A)$, для которого $overline(f)$~— изоморфизм, то $f$~—
      изоморфизм;] <cond:projective-reduction-reflects-isomorphisms>
    #condition-item(format: "cyrillic")[функтор $overline(dot)$ осуществляет
      инъективное отображение классов изоморфных объектов; оно биективно, если
      кольцо $A$ $J$-адически
      полно.] <cond:projective-reduction-isomorphism-classes>
  ]
] <prop:projective-reduction-mod-radical>

#proof[
  Если $overline(f): overline(P) -> overline(Q)$, то существует морфизм
  $f: P -> Q$, для которого следующая диаграмма коммутативна:
  $ #projective-reduction-square() $
  (тем самым показывается согласованность наших обозначений). Для нас была
  существенна проективность модуля $P$ и сюръективность отображения
  $Q -> overline(Q)$. Таким образом, наш функтор полный. Если отображение
  $overline(f)$ сюръективно, то применение леммы Накаямы к конечно порожденному
  модулю $Q$ показывает, что отображение $f$ сюръективно. Проективность модуля
  $Q$ влечет за собой расщепляемость последовательности $P limits(arrow.r)^f Q$,
  откуда следует, что прямое слагаемое $H = Ker(f)$~— конечно порожденный
  модуль. Так как $Ker(overline(f)) = 0$, то $overline(H) = 0$. Еще раз применяя
  лемму Накаямы, получим $H = 0$. Это доказывает свойство
  @cond:projective-reduction-reflects-isomorphisms и показывает, что
  $overline(P) tilde.eq overline(Q) => P tilde.eq Q$.

  Остается лишь показать, что для любого модуля $Q in bold(P)(overline(A))$
  найдется $P in bold(P)(A)$, такой, что $Q tilde.eq overline(P)$ (в
  предположении, что кольцо $A$ является $J$-адически полным). Мы можем считать,
  что $Q = Im(overline(e))$, где
  $overline(e)^2 = overline(e) in End_(overline(A)) (overline(A)^n) =
  M_n (overline(A))$. Если мы поднимем $overline(e)$ #source(86)до идемпотента
  $e in M_n (A) = End_A (A^n)$, то $P = Im(e)$, очевидно, будет решением нашей
  задачи. Так как кольцо $A$ $J$-адически полно, то
  $M_n (A) = projLim M_n (A slash J^m)$. Поэтому возможность поднять
  $overline(e)$ следует из предложения~@prop:orthogonal-idempotent-lifting.
]

#corollary[
  Если $A$~— локальное кольцо, то каждый модуль $P in bold(P)(A)$ свободен.
] <cor:local-projective-free>

#proof[
  В предыдущем предложении следует рассмотреть $J = rad A$. Тогда кольцо
  $overline(A)$ является телом и потому модуль $overline(P)$ свободен.
]

Пусть $R$~— коммутативное кольцо. Будем говорить, что идеалы $frak(a)$ и
$frak(b)$ _комаксимальны_, если $frak(a) + frak(b) = R$. В этом случае для
любого $R$-модуля $M$ включение $M frak(a) frak(b) subset
M frak(a) inter M frak(b)$ превращается в равенство. Действительно, если
$x in M frak(a) inter M frak(b)$ и $1 = a + b$ ($a in frak(a)$, $b in frak(b)$),
то $x = x a + x b in M frak(a) frak(b)$.
#idx("комаксимальные идеалы")

Предположим, что идеалы $frak(a)$ и $frak(b)_i$ комаксимальны ($1 <= i <= n$).
Пусть $1 = a_i + b_i$ ($a_i in frak(a)$, $b_i in frak(b)_i$, $1 <= i <= n$). В
произведении $1 = (a_1 + b_1) dots (a_n + b_n)$ все одночлены, кроме
$b_1 dots b_n in frak(b)_1 dots frak(b)_n$, лежат в $frak(a)$. Поэтому
$frak(a) + (product_i frak(b)_i) = R$.

#proposition(title: [«китайская теорема об остатках»])[
  Пусть идеалы $frak(a)_i$ ($1 <= i <= n$) попарно комаксимальны в коммутативном
  кольце $R$, $M in moduleCategory hyph R$. Тогда
  $
    inter.big_i M frak(a)_i = M dot (product_i frak(a)_i)
  $
  и
  $
    M -> product.co_i M slash (M frak(a)_i)
  $
  сюръективное отображение (с ядром $inter.big_i M frak(a)_i$).
] <prop:chinese-remainder-modules>
#idx("китайская теорема об остатках")

#proof[
  Случай $n = 1$ тривиален. Пусть $n > 1$. Положим
  $frak(a)'_i = product_(j != i) frak(a)_j$. Приведенное выше замечание
  показывает, что $frak(a)_i + frak(a)'_i = R$ для любого $i$. В силу
  индуктивного предположения и сделанных замечаний
  $
    M (product_i frak(a)_i) = M frak(a)_1 frak(a)'_1 = \
    = M frak(a)_1 inter M frak(a)'_1 = \
    = M frak(a)_1 inter (inter.big_(1 <= i <= n) M frak(a)_i).
  $
  Пусть заданы элементы $x_1, dots, x_n in M$. Если $1 = a_i + b_i$,
  $a_i in frak(a)_i$, $b_i in frak(a)'_i$, то $b_i equiv 1 mod frak(a)_i$,
  $b_i equiv 0 mod frak(a)_j$ при $j != i$. Таким образом, #source(
    87,
  )$sum_i x_i b_i equiv x_i mod M frak(a)_i$ ($1 <= i <= n$), что доказывает
  сюръективность отображения $M -> product.co_i M slash (M frak(a)_i)$, ядро
  которого, очевидно, равно $inter.big_i M frak(a)_i$.
]
