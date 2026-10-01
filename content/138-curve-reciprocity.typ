#import "main-defs.typ": (
  Div, E, Im, SK, SL, U, deg, idx, intervalSymbol, leftSign, maxSpec, name-idx,
  source, supp, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, lemma, proof, proposition, theorem,
)

== Законы взаимности на алгебраических кривых <sec:curve-reciprocity>

Будем предполагать здесь известными основные сведения о функциональных полях от
одной переменной.

Рассмотрим основное поле $k$ и его конечно порожденное расширение $L$, степень
трансцендентности которого над $k$ равна единице. Допустим, что
$L_(k') = k' tensor_k L$ остается полем для всех полей $k'$, являющихся
расширением поля $k$.

Через $X$ обозначим следующее множество: $frak(p) in X$ тогда и только тогда,
когда $frak(p)$ является максимальным идеалом кольца дискретного нормирования
$A_frak(p)$, такого, что $k subset A_frak(p) subset L$ и $L$ является полем
частных кольца $A_frak(p)$. Используем также обозначение
$k(frak(p)) = frac(A_frak(p), frak(p))$; это поле является конечным расширением
поля $k$ степени $deg(frak(p)) = [k(frak(p)): k]$.
#symbol-idx($k(frak(p))$, sort: "k(p)", group: "groups", order: 108)
Нормирование, соответствующее кольцу $A_frak(p)$, обозначим через $v_frak(p)$.
Но пока, за неимением лучшего термина, назовем $X$ множеством «замкнутых точек»
расширения $L / k$. Аналогично если $k'$ — расширение поля $k$ и $X_(k')$ —
множество замкнутых точек расширения $L_(k') / k'$, то рассмотрим естественную
проекцию $X_(k') -> X (= X_k)$, определенную так:
$frak(p)' |-> frak(p)' inter L$. В том случае, когда поле $k'$ сепарабельно над
$k(frak(p))$, получаем, что
$
  k' tensor_k k(frak(p))
  = product_(frak(p)' in X_(k'), frak(p)' inter L = frak(p)) k'(frak(p)').
$
В общем случае для получения правой части факторизуем левую часть по
ниль-радикалу.

#source(267)
Группа дивизоров $D(X)$ является свободной абелевой группой, порожденной
множеством $X$. Имеет место точная последовательность:
$ 0 -> U(k) -> U(L) arrow^(Div) D(X), $
<eq:curve-divisor-exact-sequence>
где $Div(a) = sum_(frak(p) in X) v_frak(p) (a) frak(p)$. Таким образом,
$v_frak(p) (a) = 0$ для почти всех $frak(p)$ и $v_frak(p) (a) = 0$ для всех
$frak(p) in X$ тогда и только тогда, когда $a in U(k)$. Также
$
  sum_(frak(p) in X) v_frak(p) (a) deg(frak(p)) = 0
  quad (a in U(L)).
$
<eq:curve-principal-divisor-degree-zero>

Если $frak(p) in X$, то определим
$ (;)_frak(p): U(L) times U(L) -> U(k), $
полагая
$ (a, b)_frak(p) = N_(k(frak(p)) slash k) (c), $
где $c$ — смежный класс в $k(frak(p))$ элемента
$(-1)^(alpha beta) frac(a^beta, b^alpha)$,
$ alpha = v_frak(p) (a), quad beta = v_frak(p) (b). $
<eq:curve-local-symbol-definition>
#symbol-idx($(;)_frak(p)$, sort: "(·,·)_p", group: "delimiters", order: 160)
В силу присутствия здесь нормы это выражение не совпадает с символом
$(a, b)_frak(p)$, введенным в @sec:dedekind-reciprocity-laws.

#proposition[
  Отображение $(;)_frak(p)$ является антисимметрическим билинейным спариванием,
  обладающим следующими свойствами:
  #condition-list[
    #condition-item(format: "cyrillic")[если $a, 1 - a in U(L)$, то
      $(a, 1 - a)_frak(p) = 1$ для всех $frak(p) in X$;]
    <cond:curve-local-steinberg>
    #condition-item(format: "cyrillic")[если $a, b in U(L)$, то
      $(a, b)_frak(p) = 1$ почти для всех $frak(p) in X$;]
    <cond:curve-local-finite-support>
    #condition-item(format: "cyrillic")[если $k'$ — расширение поля $k$, то
      $
        (a, b)_frak(p)
        = product_(frak(p)' in X_(k'), frak(p)' inter L = frak(p))
        (a, b)_(frak(p)').
      $
    ] <cond:curve-local-base-change>
  ]
] <prop:curve-local-symbol-properties>

#proof[
  Очевидно, что отображение $(;)_frak(p)$ билинейно и антисимметрично.

  @cond:curve-local-steinberg. Если $v_frak(p) (a) > 0$, то в силу приведенного
  выше определения @eq:curve-local-symbol-definition $beta = 0$ и
  $1 - a equiv 1 mod frak(p)$, т.~е. $c = 1$. Аналогично $c = 1$, если
  $v_frak(p) (1 - a) > 0$, так как ввиду антисимметрии $a = 1 - (1 - a)$. Кроме
  того, $c = 1$, если $alpha = 0 = beta$. Поэтому допустим, что $alpha < 0$.
  Тогда из «ультраметрического неравенства» для нормирований следует, что также
  $beta = alpha < 0$. Таким образом, $c^(-1)$ совпадает со смежным классом по
  модулю $frak(p)$ элемента $(-1)^(alpha^2) ((1 - a) / a)^alpha
  = (-1)^(alpha^2) (a^(-1) - 1)^alpha$, и поэтому
  $c = (-1)^(alpha^2) (-1)^alpha = 1$.

  @cond:curve-local-finite-support. Из указанной выше последовательности
  @eq:curve-divisor-exact-sequence вытекает, что $alpha = 0 = beta$ для
  большинства $frak(p)$, и для них, очевидно, $(a, b)_frak(p) = 1$.

  #source(268)
  @cond:curve-local-base-change. Заметим, что
  $
    (a, b)_frak(p) = N_(k(frak(p)) slash k) (c)
    = N_(k' tensor_k k(frak(p)) slash k') (c).
  $
  Но
  $
    k' tensor_k k(frak(p)) = product B_(frak(p)')
    quad (frak(p)' in X_(k'), quad frak(p)' inter L = frak(p)),
  $
  где $B_(frak(p)') = frac(A_(frak(p)'), frak(p) A_(frak(p)'))$, и поэтому
  $
    N_(k' tensor_k k(frak(p)) slash k') (c)
    = product_(frak(p)') N_(B_(frak(p)') slash k') (c).
  $
  Здесь норма равна определителю умножения на $c$, и в $B_(frak(p)')$ имеется
  ряд Жордана — Гёльдера длины $v_(frak(p)') (frak(p))$ с факторами
  $k'(frak(p)')$. Таким образом, получаем,
  $
    N_(B_(frak(p)') slash k') (c)
    = N_(k'(frak(p)') slash k') (c)^(v_(frak(p)') (frak(p))).
  $
  Но $c$ является смежным классом элемента
  $(-1)^(alpha beta) frac(a^beta, b^alpha)$, и поэтому
  $c^(v_(frak(p)') (frak(p)))$ — смежный класс элемента
  $(-1)^(alpha' beta') frac(a^(beta'), b^(alpha'))$, где
  $alpha' = alpha v_(frak(p)') (frak(p))
  = v_frak(p) (a) v_(frak(p)') (frak(p)) = v_(frak(p)') (a)$, и аналогично
  $beta' = v_(frak(p)') (b)$. Таким образом,
  $N_(B_(frak(p)') slash k') (c) = (a, b)_(frak(p)')$, что и требовалось
  доказать.
]

#theorem(title: [А. Вейль])[
  Если $a, b in U(L)$, то
  $ product_(frak(p) in X) (a, b)_frak(p) = 1. $
  <eq:weil-reciprocity-product-formula>
] <th:weil-reciprocity>
#idx("теорема", "А. Вейля")

Основную роль в доказательстве играет следующая лемма, осуществляющая сведение
теоремы к случаю поля рациональных функций. Заметим сначала, что в силу
@cond:curve-local-base-change достаточно доказать теорему для алгебраически
замкнутого поля $k$, и поэтому это предположение будет иметь силу до конца
доказательства.

#lemma[
  Предположим, что $K$ — подполе поля $L$, степень трансцендентности которого
  над $k$ равна единице. Пусть $Y$ — множество «замкнутых точек» расширения
  $K / k$. Если $(a, b) in U(K) times U(L)$ и если $frak(q) in Y$, то
  $
    (a, N_(L slash K) (b))_frak(q)
    = product_(frak(p) in X, frak(p) inter K = frak(q)) (a, b)_frak(p).
  $
] <lem:curve-reciprocity-norm-transfer>

#proof[
  Пусть $K_frak(q)$ — пополнение поля $K$ относительно $v_frak(q)$. Тогда
  $K_frak(q) tensor_K L
  = product_(frak(p) in X, frak(p) inter K = frak(q)) L_frak(p)$, где
  $L_frak(p)$ — пополнение $L$ по $v_frak(p)$ и
  $N_(L slash K) (b) = product N_(L_frak(p) slash K_frak(q)) (b)$. Поскольку
  символы $(;)_frak(q)$ и $(;)_frak(p)$, очевидно, продолжаются на пополнения,
  достаточно доказать каждую из локальных формул
  $ (a, N_(L_frak(p) slash K_frak(q)) (b))_frak(q) = (a, b)_frak(p). $
  <eq:curve-reciprocity-local-norm>

  #source(269)
  Известно, что эти пополнения являются полями степенных рядов от одной
  переменной над полем вычетов колец $A_frak(q)$ и $A_frak(p)$ соответственно.
  Так как мы предполагаем, что поле $k$ алгебраически замкнуто, то мы имеем поля
  степенных рядов над $k$.

  Любой обратимый элемент кольца $A_frak(q)$ является частным двух локальных
  параметров, поэтому группа $U(K_frak(q))$ порождается локальными параметрами.
  Это же верно и для $L_frak(p)$. Так как отображение
  @eq:curve-reciprocity-local-norm билинейно по $(a, b)$, достаточно проверить
  @eq:curve-reciprocity-local-norm для $(a, b) = (t, s)$, где
  $K_frak(q) = k((t))$ и $L_frak(p) = k((s))$. Положим
  $e = [L_frak(p): K_frak(q)]$, и пусть
  $ s^e + a_(e - 1) s^(e - 1) + dots + a_1 s + a_0 = 0 $
  <eq:curve-reciprocity-uniformizer-polynomial>
  — минимальный многочлен элемента $s$ над $K_frak(q)$. Тогда
  $ v_frak(p) (a_i s^i) = v_frak(q) (a_i) e + i equiv i mod e. $
  Следовательно, $v_frak(p) (a_i s^i)$ — различные числа, кроме возможного
  совпадения $v_frak(p) (s^e)$ $(= e)$ с $v_frak(p) (a_0) = e v_frak(q) (a_0)$.
  Но тогда из @eq:curve-reciprocity-uniformizer-polynomial вытекает, что
  $v_frak(q) (a_0) = 1$ и, кроме того, $v_frak(p) (a_i s^i) > e$ $(0 < i < e)$.
  Но $a_0 = (-1)^e N_(L_frak(p) slash K_frak(q)) (s)$, поэтому
  $(t, N_(L_frak(p) slash K_frak(q)) (s))_frak(q)$ является смежным классом по
  модулю $t$ (или $s$) элемента
  $(-1)^(1 dot 1) frac(t^1, ((-1)^e a_0)^1) = (-1)^(1 - e) (t / a_0)$. С другой
  стороны, $(t, s)_frak(p)$ — смежный класс по модулю $s$ элемента
  $(-1)^(e dot 1) frac(t^1, s^e)$. Таким образом, надо доказать, что
  $ (-1)^(1 - e) (t / a_0) equiv (-1)^e t / s^e mod s, $
  т.~е. что
  $ a_0 / s^e equiv -1 mod s. $
  Если мы разделим равенство @eq:curve-reciprocity-uniformizer-polynomial на
  $s^e$, то получим, что
  $ 1 + x + a_0 / s^e = 0, $
  где $x = s^(-e) (sum_(0 < i < e) a_i s^i)$. Как мы видели выше,
  $v_frak(p) (x) > 0$. Лемма доказана.
]

#proof(head: [Доказательство теоремы @th:weil-reciprocity.])[
  Как уже было замечено ранее, можно считать, что поле $k$ алгебраически
  замкнуто. Пусть $a, b in U(L)$. Если $a in k$, то в обозначениях
  @eq:curve-local-symbol-definition $alpha = 0$ для всех $frak(p)$ и
  $(a, b)_frak(p) = a^(v_frak(p) (b))$. В этом случае
  @eq:weil-reciprocity-product-formula, следовательно, сводится к формуле
  @eq:curve-principal-divisor-degree-zero: $sum v_frak(p) (b) = 0$ (поскольку
  поле $k$ алгебраически замкнуто, $deg(frak(p)) = 1$ для всех $frak(p)$).

  Если $a in.not k$, то можно применить @lem:curve-reciprocity-norm-transfer для
  поля $K = k(a)$ и свести вопрос к случаю, когда $L = k(t)$, $t$ — переменная и
  $a = t$. Кроме того, $b = b_0 product_i (t - x_i)^(n_i)$, где $b_0 in U(k)$,
  все $x_i$ лежат в $k$ #source(270)и $n_i in ZZ$. Следовательно, в силу
  линейности и рассмотренного выше случая констант можно считать, что
  $b = t - x$ $(x in k)$.

  _Случай $x = 0$._ Теперь $X$ соответствует точкам $k union {infinity}$
  (проективной прямой над $k$). Нетривиальные символы:
  $ (t, t)_0 = ((-1)^(1 dot 1) t^1 / t^1 mod t) = -1 $
  и
  $
    (t, t)_infinity
    = ((-1)^((-1)(-1)) t^(-1) / t^(-1) mod t^(-1)) = -1.
  $
  Так как $(-1)(-1) = 1$, то справедливо равенство
  @eq:weil-reciprocity-product-formula.

  _Случай $x != 0$._ Нетривиальные символы:
  $ (t, t - x)_0 = ((-1)^(1 dot 0) t^0 / (t - x)^1 mod t) = -x^(-1); $
  $ (t, t - x)_x = ((-1)^(0 dot 1) t^1 / (t - x)^0 mod (t - x)) = x; $
  $
    (t, t - x)_infinity
    = ((-1)^((-1)(-1)) t^(-1) / (t - x)^(-1) mod t^(-1)) = -1.
  $
  Так как $(-x^(-1)) dot x dot (-1) = 1$, то равенство
  @eq:weil-reciprocity-product-formula установлено и в этом случае, что
  завершает доказательство теоремы @th:weil-reciprocity.
]

В силу @prop:curve-local-symbol-properties и @th:weil-reciprocity символы
$(;)_frak(p)$ определяют закон взаимности на $X$ в смысле определения
@def:number-field-reciprocity-law. Кроме того, очевидно, что символ
$(;)_frak(p)$ удовлетворяет условию @ax:reciprocity-local-filtration из
@sec:number-field-reciprocity для всех $h >= 0$. Следовательно, можно, как и в
@prop:number-field-symbol-reciprocity, применить этот закон взаимности к
дедекиндовым кольцам следующего типа.

Пусть $S_infinity$ — конечное непустое подмножество множества $X$; положим
$
  A = inter_(frak(p) in.not S_infinity) A_frak(p)
  = {a in L bar v_frak(p) (a) >= 0 quad "для всех" quad
    frak(p) in.not S_infinity}.
$
Когда нам нужно будет уточнить обозначения, мы будем писать
$A = k[X without S_infinity]$. Известно, что $A$ — дедекиндово кольцо,
локализации которого по максимальным идеалам совпадают в точности с кольцами
$A_frak(p)$ $(frak(p) in.not S_infinity)$. Таким образом, можно отождествить
$maxSpec(A)$ с $X without S_infinity$.

Из @prop:number-field-symbol-reciprocity теперь следует, что мы получаем
$A$-взаимность (т.~е. $frak(q) = A$ в @prop:number-field-symbol-reciprocity) со
значениями в
$ frac(U(k), N_infinity), $
где $N_infinity$ — группа, порожденная
${Im(N_(k(frak(p)) slash k)) bar frak(p) in S_infinity}$.
#symbol-idx($N_infinity$, sort: "N_∞", group: "groups", order: 112)

#corollary[
  Пусть, как и выше, $A = k[X without S_infinity]$, и пусть $N_infinity$ —
  только что определенная группа. Тогда существует гомоморфизм
  $ SK_1 (A) -> frac(U(k), N_infinity), $
  образ которого порождается образами $N_(k(frak(p)) slash k) (U(k(frak(p))))$
  для всех $frak(p) in.not S_infinity$.
] <cor:curve-norm-reciprocity>

Заметим, что $N_(k(frak(p)) slash k) (U(k)) = U(k)^(deg(frak(p)))$, и поэтому
$frac(U(k), N_infinity)$ — периодическая группа экспоненты н.~о.~д.
${deg(frak(p)) bar frak(p) in S_infinity}$.

#source(271)
Следствие @cor:curve-norm-reciprocity представляет собой единственный
классический источник законов взаимности на кривых типа, возникающих здесь в
связи с группой $SK_1 (A)$. Конечно, ничего нетривиального не возникает, если
нормы $N_(k(frak(p)) slash k)$ всегда сюръективны. Например, это так, если поле
$k$ _конечно_, и действительно в этом случае верна

#theorem(title: [Басс, Милнор, Серр @bib:Bass1967a])[
  Допустим, что $k$ — конечное поле и $A$ — кольцо, рассмотренное в
  @cor:curve-norm-reciprocity. Тогда $SK_1 (A, frak(q)) = 0$ для всех идеалов
  $frak(q)$ кольца $A$.
] <th:finite-field-mennicke-triviality>
#idx("теорема", "Басса — Милнора — Серра")

Как и в @cor:arithmetic-special-linear-elementary, отсюда вытекает

#corollary[
  Если $A$ — кольцо из @th:finite-field-mennicke-triviality, то
  $SL_n (A) = E_n (A)$ для всех $n >= 3$#footnote[
    Если группа $U(A)$ бесконечна, то $SL_2 (A) = E_2 (A)$, см. Васерштейн
    @bib:Vaserstein1972. — _Прим. ред._
  ] и эти группы конечно порождены.
] <cor:finite-field-special-linear-elementary>

Можно было бы предположить, что $SK_1 (A) = 0$ также и для алгебраически
замкнутого поля $k$, так как в этом случае опять $N_infinity = U(k)$. Этот
вопрос был предложен Мамфордом. Как мы увидим в @ch:reciprocity-finiteness, это
не так. В действительности группа $SK_1 (A)$ может быть в случае алгебраически
замкнутого поля $k$ достаточно большой. Мы сможем использовать теорию, развитую
в этой главе, для получения результатов в обратном направлении и показать затем
существование неклассических законов взаимности на кривых.

В завершение этого параграфа покажем, как можно применять следствие
@cor:curve-norm-reciprocity для вычисления группы $SK_1 (A)$ в некоторых простых
случаях.

Пусть $k = RR$ и $L_1 = RR(x, y)$, где $x$ и $y$ подчинены одному соотношению:
$x^2 + y^2 = 1$. Таким образом, $A_1 = RR[x, y]$ — вещественное координатное
кольцо окружности $S^1 subset RR^2$. Фактически $S^1$ совпадает в точности с
«вещественной частью» $X_1$, т.~е. с множеством тех $frak(p) in X_1$, для
которых $k(frak(p)) = RR$. Все другие точки комплексные. Отсюда следует, что
группа $N_infinity$ из @cor:curve-norm-reciprocity совпадает с группой
$N_(CC slash RR) (U(CC))$ (которая является группой положительных действительных
чисел). Имеет место точная последовательность
$ U(CC) arrow^(N_(CC slash RR)) U(RR) arrow^("sign") frac(ZZ, 2 ZZ) -> 0. $
По техническим соображениям будем записывать знак аддитивно (так что
$"sign"(x) = 0$, если $x > 0$, $"sign"(x) = 1$, если $x < 0$). Для
$a, b in U(L)$ положим
$ [a, b]_frak(p) = "sign" (a, b)_frak(p) in frac(ZZ, 2 ZZ). $
Тогда $[a, b]_frak(p) = 0$, если точка $frak(p)$ комплексная, и поэтому формула
произведения @eq:weil-reciprocity-product-formula приводит нас к закону
взаимности на #source(272)вещественной кривой
$ sum_(t in S^1) [a, b]_t = 0. $
<eq:real-curve-sign-reciprocity>

Кроме того, имеет место, как и в @cor:curve-norm-reciprocity, гомоморфизм
$ SK_1 (RR[x, y]) -> frac(ZZ, 2 ZZ), $
который, очевидно, сюръективен (поскольку пространство $maxSpec(A_1)$ содержит
вещественные точки). В @ch:reciprocity-finiteness мы убедимся, что этот
гомоморфизм в действительности является изоморфизмом.

В одном частном случае формулу @eq:real-curve-sign-reciprocity можно записать
подробнее. Пусть $f$ и $g$ — не обращающиеся в нуль вещественные рациональные
функции на $S^1$ без общих нулей или полюсов на $S^1$. Тогда
$ product_(v_t (g) != 0) f(t)^(v_t (g)) quad (t in S^1) $
и
$ product_(v_t (f) != 0) g(t)^(v_t (f)) quad (t in S^1) $
являются ненулевыми действительными числами одного и того же знака.

Дадим теперь прямое доказательство равенства @eq:real-curve-sign-reciprocity,
преимущество которого заключается в том, что оно дает некоторые
$frak(q)$-взаимности для неединичного идеала $frak(q)$.

Если $f$ и $g$ — вещественные функции, мероморфные (и не равные тождественно
нулю) в окрестности точки $t in RR$, то, как и выше, можно записать
$
  [f, g]_t = "sign" ((-1)^(n m) (frac(f^n, g^m))(t))
  in frac(ZZ, 2 ZZ),
$
где $n = v_t (g)$ и $m = v_t (f)$. Предположим, что $a <= b$ и что $f$ и $g$
мероморфны в открытом интервале, содержащем $a$ и $b$. Тогда у них лишь конечное
число нулей и полюсов в $(a <= t <= b)$, и поэтому можно определить
$ intervalSymbol(a, f, g, b) = sum_(a <= t < b) [f, g]_t. $
#symbol-idx(
  $attach(lr([dot]), bl: a, b: b)$,
  sort: "a[·]_b",
  group: "delimiters",
  order: 165,
)
Эти символы антисимметричны и бимультипликативны по $(f, g)$ и удовлетворяют
аналогу условия @cond:curve-local-steinberg. Кроме того, если $a <= b <= c$, то
очевидно, что
$
  intervalSymbol(a, f, g, c)
  = intervalSymbol(a, f, g, b) + intervalSymbol(b, f, g, c).
$
<eq:real-interval-symbol-additivity>

#proposition[
  Пусть $f$ и $g$ — не обращающиеся в нуль вещественные мероморфные функции на
  открытом интервале, содержащем $a$ и $b$ $(a <= b)$. Тогда
  $
    intervalSymbol(a, f, g, b)
    = leftSign(a, f) leftSign(a, g) + leftSign(b, f) leftSign(b, g).
  $
  <eq:real-interval-sign-formula>
] <prop:real-interval-sign-reciprocity>

Здесь через $leftSign(x, f)$ обозначен знак числа $f(x - epsilon)$ для всех
достаточно малых $epsilon > 0$.
#symbol-idx($leftSign(x, f)$, sort: "x^f", group: "groups", order: 91)
Выражение в правой части подсчитывается в _кольце_ $frac(ZZ, 2 ZZ)$. (По этой
причине мы записывали знаки аддитивно.)

#source(273)
#proof[
  Малые сдвиги $a$ и $b$ влево, очевидно, не изменяют ни одну из частей
  равенства @eq:real-interval-sign-formula. Поэтому можно считать, что $f$ и $g$
  не имеют ни нулей, ни полюсов в $a$ или в $b$. Тогда можно разрезать интервал
  на маленькие подинтервалы с тем же самым свойством и притом так, чтобы
  внутренность каждого из них не содержала более одной особенности одной из
  наших функций. Из @eq:real-interval-symbol-additivity следует, что левая часть
  равенства @eq:real-interval-sign-formula аддитивна на интервалах, так же как и
  правая, поскольку сложение происходит в $frac(ZZ, 2 ZZ)$. Следовательно,
  достаточно показать предложение в том случае, когда в $(a <= t <= b)$ имеется
  не более одной точки, являющейся особенностью для $f$ или $g$, причем эта
  точка не является граничной. Далее, так как обе части равенства
  @eq:real-interval-sign-formula бимультипликативны по $(f, g)$, то можно
  считать, что особенности — нули первого порядка. Таким образом, мы должны
  рассмотреть следующие три случая:
  #condition-list[
    #condition-item(format: "(I)")[Ни $f$, ни $g$ не имеют особенностей. Тогда
      $leftSign(a, f) = leftSign(b, f)$, $leftSign(a, g) = leftSign(b, g)$ и
      поэтому $leftSign(a, f) leftSign(a, g)
      + leftSign(b, f) leftSign(b, g)
      = 2 leftSign(a, f) leftSign(a, g) = 0$, а тогда очевидно, что
      $intervalSymbol(a, f, g, b) = 0$.]
    <cond:real-interval-no-singularity>
    #condition-item(format: "(I)")[Точка $c$, $a < c < b$, является нулем
      первого порядка для $f$ (или для $g$), а для другой функции точка $c$ не
      является особой. Поскольку $f$ и $g$ симметрично входят в обе части
      равенства @eq:real-interval-sign-formula, можно считать, что $f(c) = 0$.
      Тогда $leftSign(b, f) = 1 - leftSign(a, f)$ (в $frac(ZZ, 2 ZZ)$, т.~е.
      знаки $leftSign(a, f)$ и $leftSign(b, f)$ противоположны) и
      $leftSign(a, g) = leftSign(b, g)$. Следовательно, правая часть равенства
      @eq:real-interval-sign-formula равна $leftSign(a, f) leftSign(a, g)
      + (1 - leftSign(a, f)) leftSign(a, g) = leftSign(a, g)$. Знак левой части
      равенства @eq:real-interval-sign-formula также равен
      $"sign"(g(c)) = leftSign(a, g)$.]
    <cond:real-interval-single-zero>
    #condition-item(format: "(I)")[Точка $c$ является нулем первого порядка
      обеих функций $f$ и $g$. Тогда $leftSign(b, f) = 1 - leftSign(a, f)$ и
      $leftSign(b, g) = 1 - leftSign(a, g)$ и поэтому правая часть
      @eq:real-interval-sign-formula равна
      $
        leftSign(a, f) leftSign(a, g)
        + (1 - leftSign(a, f))(1 - leftSign(a, g))
        = 1 - leftSign(a, f) - leftSign(a, g).
      $
      Левая же часть равенства @eq:real-interval-sign-formula такова:
      $"sign" ((-1) (f / g)(c)) = 1 + "sign" ((f / g)(c))$. Очевидно, что
      последний член равен $leftSign(a, f) - leftSign(a, g)$, ибо каждая из
      функций имеет особенности линейной функции в интервале. Итак, равенство
      @eq:real-interval-sign-formula установлено и в случае
      @cond:real-interval-common-zero, что завершает доказательство предложения
      @prop:real-interval-sign-reciprocity.]
    <cond:real-interval-common-zero>
  ]
]

Формула взаимности @eq:real-curve-sign-reciprocity является следствием
предложения @prop:real-interval-sign-reciprocity, так как можно разрезать
окружность на интервалы, каждый из которых аналитически эквивалентен
вещественному интервалу. Тогда можно применить
@prop:real-interval-sign-reciprocity и произвести сложение по интервалам. Сумма
членов правых частей в @eq:real-interval-sign-formula даст нуль, а сумма левых
частей даст левую часть в @eq:real-curve-sign-reciprocity.

Больший интерес, однако, представляет тот факт, что предложение
@prop:real-interval-sign-reciprocity приводит нас к $frak(q)$-взаимностям на
аффинной прямой для некоторых $frak(q)$. Именно пусть $L_0 = RR(T)$, где $T$ —
переменная, и пусть $A_0 = RR[T]$, $frak(q) = (T^2 - T) A_0$. Если
$f, g in U(L_0)$ и $frak(p) in X$, т.~е. это — замкнутая точка расширения
$L_0 / RR$, то определим #source(274)$lr((frac(f "," g, frak(p))))$ тривиальным
образом, кроме случая, когда $frak(p)$ соответствует точке $t$, $0 <= t < 1$, а
в этом случае положим, как и выше, $lr((frac(f "," g, frak(p)))) = [f, g]_t$.
Тогда в силу
@prop:real-interval-sign-reciprocity
$
  sum_(frak(p) in X) lr((frac(f "," g, frak(p))))
  = sum_(0 <= t < 1) [f, g]_t = intervalSymbol(0, f, g, 1)
  = leftSign(0, f) leftSign(0, g)
  + leftSign(1, f) leftSign(1, g).
$
Если $(f, g) in W_frak(q)$, то $f equiv 1 mod (T^2 - T) A_0$ и поэтому
$f(0) = 1 = f(1) > 0$. Таким образом, $leftSign(0, f) = 0 = leftSign(1, f)$, и
мы получаем формулу взаимности @eq:number-field-reciprocity-product-formula из
@def:number-field-reciprocity-law для $f, g in W_frak(q)$. Из
@prop:number-field-symbol-reciprocity потому вытекает существование
индуцированного гомоморфизма
$ SK_1 (A_0, frak(q)) -> frac(ZZ, 2 ZZ), $
<eq:affine-real-interval-mennicke-character>
образ которого порождается символами $[f, g]_t$ $(0 <= t < 1$;
$(f, g) in W_frak(q))$. Если взять $f(T) = 1 + 8 (T^2 - T)$ и
$g(T) = (T^2 - T)(T - frac(1, 2))$, то $(f, g) in W_frak(q)$ и
$[f, g]_(1/2) = "sign" (f(frac(1, 2)))$. Так как
$f(frac(1, 2)) = 1 + 8 frac(1, 2)(frac(1, 2) - 1) = -1$, то мы видим, что
отображение @eq:affine-real-interval-mennicke-character — _эпиморфизм_.
Напротив, так как $A_0 = RR[T]$ — евклидово кольцо, то $SK_1 (A_0) = 0$.

Наконец, дадим топологический способ построения приведенных выше гомоморфизмов:
$ SK_1 (RR[x, y]) -> frac(ZZ, 2 ZZ) $
и
$ SK_1 (RR[T], (T^2 - T)) -> frac(ZZ, 2 ZZ). $
Если $alpha in SL_n (A_1)$, то $alpha(t) in SL_n (RR)$ для каждого $t in S^1$ и
$alpha$ индуцирует непрерывную функцию
$ S^1 -> SL_n (RR). $
Через $[alpha]$ обозначим класс этой функции в группе $pi_1 (SL_n (RR))$. Тогда
отображение $alpha |-> [alpha]$ определяет гомоморфизм
$ SL_n (A_1) -> pi_1 (SL_n (RR)). $
Последняя группа изоморфна $ZZ$ для $n = 2$ и $frac(ZZ, 2 ZZ)$ для $n >= 3$.
Если $n >= 3$, то композиция гомоморфизмов
$
  SK_1 (A_1) = frac(SL_n (A_1), E_n (A_1))
  -> pi_1 (SL_n (RR)) tilde.eq frac(ZZ, 2 ZZ)
$
совпадает с гомоморфизмом, построенным ранее. Фактически элемент
$alpha = mat(x, y; -y, x) in SL_2 (A_1)$ отображается на образующий правой
части.

Если $alpha in SL_n (A_0, frak(q))$, то $alpha(t) in SL_n (RR)$ для
$0 <= t <= 1$ и $alpha(0) = I_n = alpha(1)$. Таким образом, опять, если мы
отождествим $S^1$ #source(275)с единичным интервалом по модулю отождествления
его двух граничных точек, то для $n >= 3$ получим эпиморфизм
$SL_n (A_0, frak(q)) -> pi_1 (SL_n (RR)) tilde.eq frac(ZZ, 2 ZZ)$, совпадающий с
рассмотренным выше отображением @eq:affine-real-interval-mennicke-character.
Этот пример был впервые рассмотрен Столлингсом, использовавшим именно эту
топологическую конструкцию.
#name-idx("Столлингс (Stallings J.)")
