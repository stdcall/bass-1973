#import "main-defs.typ": (
  Aut, E, End, Hom, Im, U, fRank, idx, maxSpec, moduleCategory, name-idx, rad,
  source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition, theorem,
)

== Сокращение, элементарные автоморфизмы
<sec:cancellation-elementary-automorphisms>

Теорема Серра дает нам критерий того, что модуль $P in moduleCategory hyph A$
имеет вид $P tilde.eq A plus.o P'$. Результаты этого параграфа позволяют дать
аналогичный критерий единственности (с точностью до изоморфизма) модуля $P'$. Мы
сохраняем определения и предположения из @ss:serre-ring-hypotheses. Кроме того,
будем предполагать, что _
$X$ является объединением конечного числа подпространств, размерность которых
$<= d$_.

#theorem[
  Пусть модули $P, Q in moduleCategory hyph A$ проективны. Допустим, что
  $fRank_A (P) > d$. Пусть $alpha = alpha_Q + alpha_P in Q plus.o P$
  ($alpha_Q in Q$, $alpha_P in P$), и пусть $frak(a)$ — левый идеал в кольце
  $A$, такой, что $frak(a) + o_(Q plus.o P) (alpha) = A$ (определение
  $o_P (alpha)$ было дано в §~@sec:semilocal-projective-modules). Тогда
  существует гомоморфизм $f: Q -> P$, такой, что
  $frak(a) + o_P (f(alpha_Q) + alpha_P) = A$.
] <th:unimodular-element-adjustment>

#proof[
  Проведем индукцию по $d$. Случай $d = 0$ будет разобран ниже по ходу дела.

  По теореме Серра @cor:serre-free-summand
  $P = overline(beta) A plus.o overline(P)$ для некоторого унимодулярного
  элемента $overline(beta) in P$. Пусть
  $alpha_P = overline(beta) b + overline(alpha)$
  ($overline(alpha) in overline(P)$). Тогда
  $A = frak(a) + o(alpha) = frak(a) + o(alpha_Q) + A b + o(overline(alpha))$.
  Пусть $D subset X$ — конечное множество, содержащее по крайней мере по одной
  точке из каждой неприводимой компоненты каждого из подпространств,
  объединением которых (как было предположено) является пространство $X$. Тогда
  если $frak(q) = inter frak(m)$ ($frak(m) in D$), то кольцо $A/(frak(q) A)$
  полулокально. Следовательно, из @prop:semilocal-unit-in-coset вытекает, что
  можно найти $c in frak(a)$, $a_Q in o(alpha_Q)$ и
  $overline(a) in o(overline(alpha))$, такие, что $c + b + a_Q + overline(a)$
  переходит в обратимый элемент кольца $A/(A frak(q))$. Из определения идеала
  $o(overline(alpha))$ следует существование гомоморфизма
  $g: overline(P) -> overline(beta) A$, такого, что
  $g(overline(alpha)) = overline(beta) overline(a)$. Продолжим $g$ до
  эндоморфизма модуля $P$, полагая $g(overline(beta)) = 0$. Тогда $g^2 = 0$;
  поэтому $sigma = 1_P + g$ является автоморфизмом и
  $sigma(alpha_P) = overline(beta)(b + overline(a)) + overline(alpha)$. Положим
  $beta = sigma^(-1)(overline(beta))$, $P_1 = sigma^(-1)(overline(P))$ и
  $alpha_1 = sigma^(-1)(overline(alpha)) in P_1$. Имеем $P = beta A plus.o P_1$
  и $alpha_P = sigma^(-1)(sigma(alpha_P)) = beta(b + overline(a)) + alpha_1$.

  #source(151)В силу определения $o(alpha_Q)$ найдется гомоморфизм
  $f_1: Q -> beta A subset P$, такой, что $f_1 (alpha_Q) = beta a_Q$. Тогда
  $
    f_1 (alpha_Q) + alpha_P = beta b_1 + alpha_1,
  $ <eq:unimodular-adjustment-first-component>
  где $b_1 = b + a_Q + overline(a)$. Как мы убедились ранее, $c + b_1$ переходит
  в обратимый элемент кольца $A/(A frak(q))$. Если
  $S = R without (union_(frak(m) in D) frak(m))$, то кольцо $S^(-1) R$
  полулокально (его максимальные идеалы находятся в соответствии с идеалами из
  $D$) и $(S^(-1) A)/(frak(q) dot (S^(-1) A)) = A/(frak(q) dot A)$ (напомним,
  что $frak(q) = inter_(frak(m) in D) frak(m)$). Кроме того,
  $frak(q) dot (S^(-1) A) subset rad(S^(-1) A)$ и потому
  $c + b_1 in U(S^(-1) A)$.

  Если $d = 0$, то $D = X$ и, следовательно, $c + b_1 in U(A)$, чем и
  завершается доказательство в этом случае.

  Если $d != 0$, то все же $S^(-1)(frak(a) + A b_1) = S^(-1) A$ и можно найти
  элемент $t in S$, такой, что
  $
    A t subset frak(a) + A b_1.
  $ <eq:unimodular-adjustment-localization-denominator>
  Введем обозначения: $R' = R/(R t)$, $A' = A/(A t)$, $frak(a)'$ — образ
  $frak(a)$ в $A'$ и т.~д. Тогда множество $X' = maxSpec(R') = V(R t)$ не
  пересекается с $D$ и, значит, является замкнутым множеством в $X$, не
  содержащим неприводимых компонент ни одного из данных подпространств,
  объединение которых совпадает с $X$. Следовательно, $X'$ является объединением
  пересечений $X'$ с этими подпространствами, а размерность этих пересечений
  строго меньше, чем размерность их аналогов в $X$. Таким образом, $X'$ есть
  объединение конечного числа подпространств, размерность каждого из которых
  $<= d - 1$. Кроме того, из @prop:localized-free-rank-additivity видно, что
  $
    fRank_(A') (P'_1) >= fRank_A (P_1) = fRank_A (P) - 1 > d - 1.
  $
  Рассмотрим $gamma' = alpha'_Q + alpha'_1 in Q' plus.o P'_1$. Так как
  $A = frak(a) + o(alpha) = frak(a) + o(alpha_Q) + A b_1 + o(alpha_1)$, то
  $A' = frak(a)' + o(gamma') + A' b'_1$. Но теперь мы в состоянии применить
  предположение индукции к $gamma' in Q' plus.o P'_1$ и левому идеалу
  $frak(a)' + A' b'_1$. Получим гомоморфизм $h': Q' -> P'_1$, такой, что
  $frak(a)' + A' b'_1 + o'_(P'_1) (h'(alpha'_Q) + alpha'_1) = A'$ (где
  $o'_M (delta) = {g delta | g in Hom_(A') (M, A')}$ для
  $M in moduleCategory hyph A'$ и $delta in M$). Так как модуль $Q$ проективен,
  то можно накрыть $h'$ гомоморфизмом $h: Q -> P_1$ ($P_1 subset P$). Теперь
  рассмотрим
  $
    f = mat(f_1; h): Q -> P = beta A plus.o P_1.
  $
  Осталось показать, что $frak(a) + frak(b) = A$, где
  $frak(b) = o(f(alpha_Q) + alpha_P)$. Используя приведенное выше равенство
  @eq:unimodular-adjustment-first-component, видим, что
  $f(alpha_Q) + alpha_P = (h(alpha_Q) + f_1 (alpha_Q)) + alpha_P
  = h(alpha_Q) + (beta b_1 + alpha_1) = beta b_1 + (h(alpha_Q) + alpha_1)
  in beta A plus.o P_1$. Так как модуль $P_1$ проективен, то естественный
  гомоморфизм #source(152)$o_(P_1) (h(alpha_Q) + alpha_1) ->
  o'_(P'_1) (h'(alpha'_Q) + alpha'_1)$ сюръективен. Таким образом, мы построили
  отображение $h'$ такое, что
  $frak(a)' + A' b'_1 + o'_(P'_1) (h'(alpha'_Q) + alpha'_1) = A' = A/(A t)$.
  Следовательно, можно утверждать, что
  $
    frak(a) + frak(b) + A t
    = frak(a) + A b_1 + o_(P_1) (h(alpha_Q) + alpha_1) + A t = A.
  $
  Так как $A t subset frak(a) + A(b_1)$ (см.
  @eq:unimodular-adjustment-localization-denominator)
  $subset frak(a) + frak(b)$, то $frak(a) + frak(b) = A$. Доказательство
  завершено.
]

#corollary[
  В предположениях теоремы @th:unimodular-element-adjustment допустим, что
  $Q = gamma A$ для некоторого унимодулярного элемента $gamma$, скажем
  $alpha = gamma q + alpha_P$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[$P = beta A plus.o P'$ для некоторого
      унимодулярного элемента
      $beta in P$;] <cond:relative-adjustment-free-summand>

    #condition-item(format: "cyrillic")[если
      $alpha equiv beta mod (gamma A plus.o P) frak(q)$ для некоторого
      двустороннего идеала $frak(q)$, то найдется элемент $gamma' in P frak(q)$,
      такой, что $o_P (gamma' q + alpha_P) + frak(a) = A$.]
    <cond:relative-adjustment-congruence>
  ]
] <cor:relative-unimodular-adjustment>

#proof[
  @cond:relative-adjustment-free-summand Это утверждение следует из теоремы
  Серра.

  @cond:relative-adjustment-congruence Так как $alpha equiv beta$ ($in P$)
  $mod (gamma A plus.o P) frak(q)$, то $q in frak(q)$. В силу наших
  предположений (см. теорему @th:unimodular-element-adjustment) найдутся
  гомоморфизм $h: gamma A plus.o P -> A$ и элемент $a in frak(a)$, такие, что
  $1 = h(gamma) q + h(alpha_P) + a$. Следовательно,
  $q = r + q h(alpha_P) + q a$, где $r = q h(gamma) q$. Положим
  $alpha' = gamma r + alpha_P$. Тогда
  $
    q in frak(a) + o(alpha') = frak(a) + A r + o(alpha_P)
    subset frak(a) + A q + o(alpha_P) = frak(a) + o(alpha)
  $
  и поэтому $frak(a) + o(alpha') = frak(a) + o(alpha)$. Следовательно, можно
  применить теорему @th:unimodular-element-adjustment к $alpha'$ и $frak(a)$ и
  убедиться в существовании гомоморфизма $f: gamma A -> P$, такого, что
  $o(f(gamma r) + alpha_P) + frak(a) = A$. Так как
  $f(gamma r) = f(gamma) q h(gamma) q$, то мы видим, что элемент
  $gamma' = f(gamma) q h(gamma) in P frak(q)$ дает решение нашей задачи.
]

Введем теперь некоторые новые понятия и обозначения, которые будут использованы
в следующей теореме, а также в следующей главе. Для этих определений наши
предположения @ss:serre-ring-hypotheses о кольце $A$ не нужны.

Пусть $M in moduleCategory hyph A$ есть прямая сумма
$M = M_1 plus.o dots plus.o M_n$. Тогда $End_A (M)$ — прямая сумма групп
$Hom_A (M_i, M_j)$; при этом мы отождествляем гомоморфизм
$h in Hom_A (M_i, M_j)$ с его продолжением на модуль $M$, задаваемым формулами
$h(M_k) = 0$ при $k != i$. Если $i != j$, то $g h = 0$, как только
$g, h in Hom_A (M_i, M_j)$ и, следовательно, $(1_M + g)(1_M + h) = 1_M + g + h$.
Получаем гомоморфизм $Hom_A (M_i, M_j) -> Aut_A (M)$ для каждой пары индексов
$i != j$. Группу, порожденную образами этих гомоморфизмов для всех $i != j$,
обозначим через $E(M_1, dots, M_n)$.

Если $h in Hom_A (M_i, M_j)$ ($i != j$), то назовем $1_M + h$ _элементарным
автоморфизмом_#idx("элементарный автоморфизм") (относительно разложения
$M = M_1 plus.o dots #source(153)plus.o M_n$). Если $frak(q)$ — двусторонний
идеал в $A$, то назовем автоморфизм $1_M + h$ _$frak(q)$-элементарным_,#idx(
  "q-элементарный автоморфизм",
) если $Im(h) subset M frak(q)$. Через
$
  E(M_1, dots, M_n; frak(q))
$
обозначим _нормальную подгруппу_ группы $E(M_1, dots, M_n)$, порожденную всеми
$frak(q)$-элементарными автоморфизмами.

#proposition[
  Пусть $P = P_1 plus.o dots plus.o P_n$ — проективный правый $A$-модуль,
  $frak(q)$ — двусторонний идеал кольца $A$ и $f: A -> A'$ — сюръективный
  гомоморфизм колец. Тогда индуцированный гомоморфизм
  $
    E(P_1, dots, P_n; frak(q)) -> E(P'_1, dots, P'_n; frak(q)')
  $
  сюръективен. Здесь $frak(q)' = f(frak(q))$ и $P'_i = P_i tensor_A A'$
  ($1 <= i <= n$).
] <prop:elementary-group-quotient-surjection>

#proof[
  Так как отображение $P_j frak(q) -> P'_j frak(q)'$ сюръективно, то любой
  гомоморфизм $h': P'_i -> P'_j frak(q)'$ поднимается до гомоморфизма
  $h: P_i -> P_j frak(q)$, поскольку модуль $P_i$ проективен. Это показывает,
  что все $frak(q)'$-элементарные автоморфизмы могут быть подняты. В частном
  случае $frak(q) = A$ это показывает, что отображение
  $E(P_1, dots, P_n) -> E(P'_1, dots, P'_n)$ сюръективно. Но группа
  $E(P'_1, dots, P'_n; frak(q)')$ порождается элементами вида
  $sigma' tau' sigma'^(-1)$, где $sigma' in E(P'_1, dots, P'_n)$ и автоморфизм
  $tau'$ является $frak(q)'$-элементарным. Мы можем поднять $tau'$ до
  $frak(q)$-элементарного автоморфизма $tau$ и $sigma'$ до элемента
  $sigma in E(P_1, dots, P_n)$. Следовательно,
  $sigma tau sigma^(-1) in E(P_1, dots, P_n; frak(q))$ является желаемым
  прообразом элемента $sigma' tau' sigma'^(-1)$. Предложение доказано.
]

Вернемся теперь к нашим постоянным предположениям @ss:serre-ring-hypotheses о
кольце $A$. Заметим, что $d$ сохраняет свое значение из теоремы
@th:unimodular-element-adjustment.

#theorem[
  Пусть $M = gamma A plus.o M_1$, где $M in moduleCategory hyph A$, элемент
  $gamma$ унимодулярен в $M$ и модуль $M_1$ содержит проективное прямое
  слагаемое $P$, для которого $fRank(P) > d$. Пусть $frak(q)$ — двусторонний
  идеал кольца $A$ и $alpha, alpha' in M$ — унимодулярные элементы, такие, что
  $alpha equiv alpha' mod M frak(q)$. Тогда существует автоморфизм
  $tau in E(gamma A, M_1; frak(q))$, такой, что $tau alpha = alpha'$.
] <th:elementary-unimodular-transitivity>

#proof[
  Пусть $M_1 = P plus.o N$ для некоторого модуля $N$. В силу теоремы Серра
  $P = beta A plus.o P'$ для некоторого унимодулярного элемента $beta in P$.

  _Частный случай: $alpha' = beta$._ Запишем $alpha = gamma q + alpha_(M_1)$
  ($alpha_(M_1) in M_1$) и $alpha_(M_1) = alpha_P + alpha_N$ ($alpha_P in P$,
  $alpha_N in N$). В силу @cor:relative-unimodular-adjustment
  @cond:relative-adjustment-congruence найдется элемент $gamma' in P frak(q)$,
  такой, что $o(gamma' q + alpha_P) + o(alpha_N) = A$.

  *Замечание.* Лишь в этом месте используется предположение относительно
  $fRank_A (P)$ (для того чтобы применить @cor:relative-unimodular-adjustment,
  @cond:relative-adjustment-congruence к $gamma q + alpha_P$ (с
  $frak(a) = o(alpha_N)$) и записать модуль $P$ в виде $P = beta A plus.o P'$).
  #source(154)Если считать выполненными эти заключения следствия
  @cor:relative-unimodular-adjustment, то наши постоянные предположения о кольце
  $A$ и модуле $P$ (касающиеся $R$ и $X$) нигде более не применяются. Это
  замечание будет использовано в следующей главе.

  Определим $g_1: M -> M$, полагая $g_1 (gamma) = gamma'$ и $g_1 (M_1) = 0$.
  Очевидно, что $tau_1 = 1_M + g_1 in E(gamma A, M_1; frak(q))$. Кроме того,
  $tau_1 (alpha) = gamma q + g_1 (gamma q) + alpha_(M_1)
  = gamma q + (gamma' q + alpha_P) + alpha_N$. Запишем
  $gamma' q + alpha_P = beta b + alpha' in P = beta A plus.o P'$
  ($alpha' in P'$). В силу построения элемент
  $delta = gamma' q + alpha_P + alpha_N = beta b + alpha' + alpha_N$
  является унимодулярным в модуле $P plus.o N = M_1$ и поэтому
  $M_1 = delta A plus.o M'_1$. Определим $g_2: M -> M$, полагая
  $g_2 (delta) = gamma(1 - b - q)$ и $g_2 (gamma A) = g_2 (M'_1) = 0$. Так как
  $alpha equiv beta mod M frak(q)$, то $b equiv 1 mod frak(q)$ и, следовательно,
  $tau_2 = 1_M + g_2 in E(gamma A, M_1; frak(q))$. Кроме того,
  $tau_2 tau_1 (alpha) = tau_2 (gamma q + delta) = gamma(1 - b) + delta
  = gamma(1 - b) + beta b + alpha' + alpha_N$.

  Определим $g_3, g_4: M -> M$, полагая $g_3 (gamma) = beta$, $g_3 (M_1) = 0$ и
  $g_4 (beta) = gamma(b - 1)$, $g_4 (gamma A) = 0 = g_4 (P' plus.o N)$. Тогда
  $tau_3 = 1_M + g_3 in E(gamma A, M_1)$ и
  $tau_4 = 1_M + g_4 in E(gamma A, M_1; frak(q))$. Кроме того,
  $sigma = tau_3^(-1) tau_4 tau_3 tau_2 tau_1 in E(gamma A, M_1; frak(q))$ и
  $
    sigma(alpha)
    & = tau_3^(-1) tau_4 tau_3 (gamma(1 - b) + beta b + alpha' + alpha_N) \
    & = tau_3^(-1) tau_4 (gamma(1 - b) + beta + alpha' + alpha_N) \
    & = tau_3^(-1)(beta + alpha' + alpha_N) = beta + alpha' + alpha_N.
  $
  Наконец, определим $g_5, g_6: M -> M$, полагая $g_5 (beta) = gamma$,
  $g_5 (gamma A) = 0 = g_5 (P' plus.o N)$ и $g_6 (gamma) = -(alpha' + alpha_N)$,
  $g_6 (M_1) = 0$. Тогда $tau_5 = 1 + g_5 in E(gamma A, M_1)$ и
  $tau_6 = 1_M + g_6 in E(gamma A, M_1; frak(q))$ и, значит,
  $tau_5^(-1) tau_6 tau_5 in E(gamma A, M_1; frak(q))$. Кроме того,
  $tau_5^(-1) tau_6 tau_5 sigma(alpha)
  = tau_5^(-1) tau_6 (gamma + beta + alpha' + alpha_N)
  = tau_5^(-1)(gamma + beta) = beta$. Этим заканчивается разбор случая 1.

  _Общий случай._ Применим результат частного случая к $frak(q) = A$. Получим,
  что найдется элемент $sigma in E(gamma A, M_1)$, такой, что
  $sigma alpha' = beta$. Еще раз применим этот результат к
  $sigma alpha equiv beta mod M frak(q)$ и получим элемент
  $tau in E(gamma A, M_1; frak(q))$, такой, что
  $tau sigma alpha = beta = sigma alpha'$. Тогда элемент
  $sigma^(-1) tau sigma in E(gamma A, M_1; frak(q))$ дает решение нашей задачи.
  Теорема доказана.
]

#corollary(title: [теорема о сокращении])[
  #idx("теорема о сокращении")Предположим, что модуль
  $M in moduleCategory hyph A$ содержит проективное прямое слагаемое $P$, для
  которого $fRank P > d$. Тогда если $M' in moduleCategory hyph A$ и
  $Q in bold(P)(A)$, то
  $
    Q plus.o M tilde.eq Q plus.o M' => M tilde.eq M'.
  $
] <cor:projective-cancellation>

#proof[
  Проведя индукцию по $n$, где $Q plus.o Q' tilde.eq A^n$, сведем нашу задачу к
  случаю $Q = A$. Используя изоморфизм для отождествления модулей, получаем, что
  $alpha A plus.o M = alpha' A plus.o M'$, где элементы $alpha$ и $alpha'$
  унимодулярны. Теперь можно применить теорему
  @th:elementary-unimodular-transitivity (с $alpha = gamma$, $M = M_1$, в
  обозначениях этой теоремы) для нахождения автоморфизма $sigma$, такого, что
  #source(155)$sigma alpha = alpha'$. Следовательно,
  $
    M tilde.eq (alpha A plus.o M)/(alpha A)
    tilde.eq (alpha A plus.o M)/sigma(alpha A)
    = (alpha' A plus.o M')/(alpha' A) tilde.eq M'.
  $
]

#corollary[
  Пусть модуль $M$ таков же, как в теореме
  @th:elementary-unimodular-transitivity, и пусть $frak(a)$ — двусторонний идеал
  кольца $A$. Положим $A' = A/frak(a)$ и $M' = M/(M frak(a))$. Если $alpha'$ —
  унимодулярный элемент в $M'$ (как $A'$-модуле), то существует унимодулярный
  элемент $alpha$ в $M$, образ которого по модулю $M frak(a)$ совпадает с
  $alpha'$.
] <cor:unimodular-quotient-lifting>

#proof[
  Применяя теорему @th:elementary-unimodular-transitivity к модулю $M'$ над
  кольцом $A'$ (все предположения, очевидно, выполнены), найдем элемент
  $tau' in E(gamma' A', M'_1)$, такой, что $tau' gamma' = alpha'$. Теперь
  воспользуемся предложением @prop:elementary-group-quotient-surjection и
  поднимем $tau'$ до $tau in E(gamma A, M_1)$. Тогда элемент $alpha = tau gamma$
  и даст решение нашей задачи.
]

#corollary[
  Пусть $M$ и $frak(q)$ те же, что и в теореме
  @th:elementary-unimodular-transitivity. Предположим, что
  $M = gamma' A plus.o M'_1$ для некоторого унимодулярного элемента $gamma'$.
  Тогда
  $
    E(gamma' A, M'_1; frak(q)) = E(gamma A, M_1; frak(q)).
  $
] <cor:elementary-group-splitting-independence>

#proof[
  Из теоремы @th:elementary-unimodular-transitivity вытекает существование
  автоморфизма $sigma in E(gamma A, M_1)$, такого, что $sigma gamma = gamma'$.
  Из определений следует, что
  $
    E(gamma A, M_1; frak(q)) = sigma E(gamma A, M_1; frak(q)) sigma^(-1)
    = E(gamma' A, sigma M_1; frak(q)).
  $
  Следовательно, можно считать, что $gamma = gamma'$. Определим $g: M -> M$,
  полагая $g(gamma) = 0$ и $g bar M_1 = p bar M_1$, где $p$ — проекция модуля
  $gamma A plus.o M'_1$ на $gamma A$. Тогда $tau = 1_M - g in E(gamma A, M_1)$ и
  $tau M_1 = M'_1$. Следовательно,
  $E(gamma A, M_1; frak(q)) = tau E(gamma A, M_1; frak(q)) tau^(-1)
  = E(gamma A, M'_1; frak(q))$.
]

#corollary[
  Пусть модуль $P in bold(P)(A)$ таков, что для каждого $frak(m) in X$ модуль
  $P_frak(m)$ порождается (над $A_frak(m)$) $<= r$ элементами. Тогда модуль $P$
  порождается $<= r + d$ элементами.
] <cor:projective-generator-bound>

#proof[
  Запишем $P plus.o Q tilde.eq A^(r+n)$ для некоторого $n >= 0$. Достаточно
  показать, что здесь можно взять $n <= d$. Предположим противное. Если
  $frak(m) in X$, то по предположению $P_frak(m) plus.o P' tilde.eq A_frak(m)^r$
  для некоторого $P'$. Так как кольцо $A_frak(m)$ полулокально, то из
  @cor:semilocal-projective-cancellation следует, что
  $Q_frak(m) tilde.eq P' plus.o A_frak(m)^n$. Итак, $fRank_A (Q) >= n > d$.
  Поэтому из теоремы Серра @cor:serre-free-summand вытекает, что
  $Q tilde.eq Q' plus.o A$. Так как $P plus.o Q' plus.o A tilde.eq A^(r+n)$, то
  $(P plus.o Q')_frak(m) tilde.eq A_frak(m)^(r+n-1)$ для каждого $frak(m) in X$
  (опять в силу @cor:semilocal-projective-cancellation). Если $r = 0$, то
  $P = 0$, и все доказано. В противном случае $r + n - 1 > d$, и мы можем
  применить теорему о сокращении @cor:projective-cancellation. Получим тогда,
  что $P plus.o Q' tilde.eq A^(r+n-1)$. Наше утверждение получается теперь по
  индукции.
]

#source(156)*Замечание.* Как показал недавно Суон @bib:Swan1967, #name-idx(
  "Суон (Swan R.)",
)утверждение @cor:projective-generator-bound справедливо и без предположения о
проективности модуля $P$.
