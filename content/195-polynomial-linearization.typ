#import "main-defs.typ": (
  E, End, GL, K, U, ed-note, idx, name-idx, semidirect, source, symbol-idx,
  tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, numbered-condition, proof,
  proposition,
)

== Линеаризация в группе $GL (A[T])$ <sec:polynomial-linearization>

#idx("линеаризация")Название относится к следующему хорошо известному методу,
происхождение которого я не смог установить (см., например, статью
Хигмана#name-idx("Хигман (Higman G.)") @bib:Higman1940).

#proposition[
  Пусть $R$ — подкольцо кольца $A$ и $M subset A$ — $R$-бимодуль, который вместе
  с $R$ порождает $A$ как кольцо. Пусть $A_+ = A M A$ — $A$-идеал, порождённый
  $M$.#symbol-idx($A_+$, sort: "subscript +", group: "subscripts", order: 156)
  Предположим, что $alpha = (a_(i j))$ $(i, j >= 1)$ — «формально бесконечная»
  матрица над $A$, т.~е. матрица, в которой $a_(i j) = delta_(i j)$ для всех
  достаточно больших $i$ и $j$. Тогда существуют
  $epsilon_1, epsilon_2 in E (A, A_+)$, для которых
  $epsilon_1 alpha epsilon_2 = alpha_0 + alpha_1$, где $alpha_0$ — формально
  бесконечная матрица над $R$, #source(492)а все коэффициенты матрицы $alpha_1$
  лежат в $M$. Если $alpha in GL (A)$, то можно добиться того, чтобы
  $epsilon_1 = I$.
] <prop:higman-linearization>

#proof[
  Из наших предположений следует, что $A$ является факторалгеброй тензорной
  алгебры $T_R (M)$. Таким образом, $A = sum M^d$ $(d >= 0)$, где $M^0 = R$ и
  $M^(d+1) = M^d dot M$. Можно записать $alpha = mat(beta, 0; 0, I)$, где $beta$
  — $(n times n)$-матрица для некоторого $n$. Далее,
  $beta = beta_0 + dots + beta_d$ для некоторого $d >= 0$, где коэффициенты у
  $beta_i$ лежат в $M^i$ $(0 <= i <= d)$. Докажем предложение, проведя индукцию
  по $d$. Если $d <= 1$, то можно взять $epsilon_1 = I = epsilon_2$. Поэтому
  допустим, что $d > 1$. Тогда можно записать: $beta_d = sum gamma_j x_j$
  $(1 <= j <= m)$, где $x_j in M$ и коэффициенты у $gamma_j$ лежат в $M^(d-1)$
  $(1 <= j <= m)$. Теперь в кольце матриц порядка $n(m+1)$ умножим матрицу
  $mat(beta, 0; 0, I_(n m))$ сначала слева, а затем справа на элементы из
  $E (A,A_+)$ и получим
  $
    mat(beta, 0; 0, I_(n m)) mapsto
    mat(beta, mat(delim: #none, gamma_1, dots, gamma_m); 0, I_(n m)) mapsto
    beta' = mat(
      beta-beta_d, mat(delim: #none, gamma_1, dots, gamma_m);
      vec(delim: #none, -I_n x_1, dots.v, -I_n x_m), I_(n m)
    ).
  $
  В том случае, когда матрица $beta$ обратима, мы можем получить первое
  преобразование также и умножением справа. Так как «степень» матрицы $beta'$
  будет $<= d-1$, то можно закончить этот процесс по индукции.
]

#proposition[
  Пусть $A = union.sq.big_(n >= 0) A_n$ — градуированное кольцо, и пусть
  $A_+ = union.sq.big_(n > 0) A_n$.
  #condition-list[
    #condition-item(format: "cyrillic")[Если $a in A_1$, то
      $[1-a in U (A)] <=> [a "— нильпотентный элемент"]$.]
    <cond:graded-one-minus-unit-nilpotence>
    #condition-item(format: "cyrillic")[Если $A_0$ и $A_1$ порождают $A$ как
      кольцо и если $alpha in GL (A)$, то можно представить $alpha$ в виде
      $ alpha = alpha_0 (I+v) epsilon, $
      где $alpha_0 in GL (A_0)$, $epsilon in E (A,A_+)$ и $v$ — матрица с
      коэффициентами из $A_1$. Такая матрица $v$ обязательно нильпотентна.]
    <cond:graded-linear-unipotent-factorization>
  ]
] <prop:graded-linear-unipotent-factorization>

#proof[
  @cond:graded-one-minus-unit-nilpotence Если элемент $a$ нильпотентен, то
  $(1-a)^(-1) = sum_(i >= 0) a^i in A$. Обратно, предположим, что
  $(1-a)^(-1) = sum b_i in A$ $(b_i in A_i)$. Тогда
  $ 1 = (1-a)(sum b_i) = b_0 + (b_1-a b_0) + (b_2-a b_1) + dots. $
  #source(493)По индукции получаем $b_i = a^i$. Таким образом, $a^i = b_i = 0$
  для достаточно больших $i$.

  @cond:graded-linear-unipotent-factorization Можно применить
  @prop:higman-linearization в случае, когда $R = A_0$ и $M = A_1$. Тогда
  получим матрицу $epsilon in E (A,A_+)$, для которой
  $alpha epsilon^(-1) = alpha_0 + alpha_1$, где коэффициенты у $alpha_i$ лежат в
  $A_i$ $(i = 0,1)$. Факторизуя по идеалу $A_+$, мы видим, что
  $alpha_0 in GL (A_0)$. Поэтому можно записать:
  $alpha epsilon^(-1) = alpha_0 (I+v)$, где $v = alpha_0^(-1) alpha_1$. Пусть
  $v = mat(v', 0; 0, 0)$, где $v' in M_n (A_1)$ для некоторого $n$. Так как
  $I_n + v' in GL_n (A) = U (M_n (A))$, то из части
  @cond:graded-one-minus-unit-nilpotence следует, что матрица $v'$, а
  следовательно, и матрица $v$ нильпотентны.
]

#corollary[
  Пусть $A$ — кольцо из @prop:graded-linear-unipotent-factorization
  @cond:graded-linear-unipotent-factorization. Тогда
  $ K_1 (A) = K_1 (A_0) plus.o K_1 (A,A_+) $
  и каждый элемент группы $K_1 (A,A_+)$ представим унипотентной матрицей $I+v$,
  где коэффициенты матрицы $v$ лежат в $A_1$. Кроме того:
  #condition-list[
    #condition-item(format: "cyrillic")[если $n A_1 = 0$ для некоторого $n > 0$,
      то порядок любого элемента группы $K_1 (A,A_+)$ конечен и делит некоторую
      степень числа $n$;]
    <cond:graded-relative-k-one-bounded-torsion>
    #condition-item(format: "cyrillic")[если кольцо $A$ регулярно справа, то
      $K_1 (A,A_+) = 0$.]
    <cond:graded-relative-k-one-regular-vanishing>
  ]
] <cor:graded-relative-k-one-unipotents>

#proof[
  Разложение в прямую сумму вытекает из @lem:split-extension-abelianization,
  поскольку $GL (A) = GL (A,A_+) semidirect GL (A_0)$ является полупрямым
  произведением. Утверждение относительно унипотентных элементов следует
  непосредственно из @prop:graded-linear-unipotent-factorization
  @cond:graded-linear-unipotent-factorization.

  @cond:graded-relative-k-one-bounded-torsion Предположим, что
  $alpha = I+beta in GL_n (A)$, где коэффициенты матрицы $beta$ лежат в $A_1$ и,
  следовательно, $beta$ — нильпотентная матрица. Через $R$ обозначим
  (коммутативное) подкольцо в кольце $M_n (A)$, порождённое $I$ и $beta$. Пусть
  $frak(a)$ — нильпотентный идеал $beta R$. По предположению $n frak(a) = 0$.
  Пусть $frak(a)^(d+1) = 0$. Тогда из @prop:nilpotent-units-finiteness
  @cond:nilpotent-unit-exponent-bound следует, что $(I+beta)^(n^d) = I$.

  @cond:graded-relative-k-one-regular-vanishing В силу
  @cor:regular-k-one-nilpotent-invariance это немедленно вытекает из первого
  утверждения.
]

#corollary[
  Пусть $A$ — регулярное справа кольцо, и пусть $T$ — свободная абелева
  полугруппа. Тогда отображение
  $ K_1 (A) -> K_1 (A[T]) $
  является изоморфизмом.
] <cor:regular-polynomial-k-one>

#proof[
  Кольцо $A[T]$ является кольцом многочленов от многих переменных, и поэтому в
  нём можно рассмотреть естественную градуировку. Кроме того, из теоремы о
  сизигиях (@th:swan-polynomial-regularity) следует, что кольцо $A[T]$ регулярно
  справа. Таким образом, следствие вытекает из
  @cor:graded-relative-k-one-unipotents
  @cond:graded-relative-k-one-regular-vanishing.
]

#source(494)Замечание. Отметим, что в приведённом утверждении $T$ не может быть
группой. Следующие два параграфа посвящаются анализу группы $K_1 (A[t,t^(-1)])$.
Непосредственно применяя технику этого параграфа, можно получить некоторые
частные результаты, например предложение
@prop:subdirect-polynomial-k-one-torsion ниже.

#corollary(title: "Герстен")[
  #idx("теорема Герстена")Пусть кольцо $A$ то же, что и в
  @cor:regular-polynomial-k-one, и пусть $M$ — $A$-бимодуль, изоморфный
  копроизведению экземпляров $A$. Пусть $B = T_A (M)$ — тензорная алгебра
  бимодуля $M$ над $A$. Тогда отображение
  $ K_1 (A) -> K_1 (T_A (M)) $
  оказывается изоморфизмом.
] <cor:gersten-tensor-algebra-k-one>

Замечание. Если $X$ является $A$-базисом для $M$, то $T_A (M)$ — свободная
ассоциативная алгебра над $A$, порождённая множеством $X$. Эквивалентно, это —
полугрупповая алгебра над кольцом $A$ свободной (некоммутативной) полугруппы,
порождённой множеством $X$.

#proof[
  $B = A plus.o M plus.o (M tensor M) plus.o dots$ является градуированным
  кольцом, порождённым бимодулем $M$ над $A$. Следовательно, как и в
  @cor:graded-relative-k-one-unipotents, $K_1 (B) = K_1 (A) plus.o K_1 (B,B_+)$,
  где $B_+$ — идеал, порождённый $M$. Кроме того, каждый элемент группы
  $K_1 (B,B_+)$ обладает представителем вида $I+v in GL_n (B)$ для некоторого
  $n$, где коэффициенты матрицы $v$ лежат в $M$. Нам надо показать, что
  $I+v in E (B)$. Пусть $(x_i)_(i in J)$ — базис бимодуля $M$. Таким образом,
  элементы $x_i$ коммутируют с элементами кольца $A$, но не друг с другом.
  Запишем $v = sum alpha_i x_i$ $(1 <= i <= n)$, где $alpha_i in M_n (A)$. Тогда
  $v^m = 0$ для всех достаточно больших $m$. Одночлены от $x_i$ образуют
  свободную полугруппу, элементы которой линейно независимы над $A$.
  Следовательно, раскрывая $v^m$ и полагая коэффициенты каждого одночлена от
  $x_i$ равными нулю, получим, что произведение любых $m$ элементов $alpha_i$
  равно нулю. Проведя индукцию по $m$, покажем теперь, что $I+v$ является
  произведением матриц вида $I+alpha w$, где $alpha$ — нильпотентная матрица над
  $A$, а $w$ — одночлен от $x_i$. Действительно, рассмотрим
  $ I+v' = (I-alpha_1 x_1) dots (I-alpha_n x_n)(I+v). $
  Можно записать $v' = sum beta_j y_j$ $(1 <= j <= s)$, где все $beta_j y_j$
  являются одночленами степени $>= 2$ от $alpha_i x_i$. Следовательно, любое
  произведение не менее чем $m/2$ элементов $beta_j$ равно нулю. Применяя
  индукцию к $I+sum beta_j z_j$, где $z_j$ — новые переменные, порождающие
  свободную алгебру над $A$, получим, что $I+v'$ является произведением матриц
  вида $I+gamma w$, где $gamma$ — нильпотентная матрица над $A$, а $w$ —
  одночлен от $y_j$ и, следовательно, также от $x_i$. Для завершения
  доказательства нам надо показать, что $I+alpha w in E (B)$, если $alpha$ —
  нильпотентная матрица над кольцом $A$, #source(495)а $w$ — одночлен от $x_i$.
  Но из @cor:regular-polynomial-k-one следует, что $I+alpha w in E (A[w])$.
  Следствие доказано.
]

В частном случае, который возникнет в одном из наших вычислений, можно следующим
образом уточнить следствия @cor:graded-relative-k-one-unipotents и
@cor:regular-polynomial-k-one.

#proposition[
  Пусть $A$ — подкольцо кольца $B = product A_i$, причём проекция кольца $A$ в
  каждое из колец $A_i$ сюръективна. Допустим, что кольцо $B$ регулярно справа и
  что $N B subset A$ для некоторого целого числа $N > 0$. Пусть $T$ — свободная
  абелева полугруппа и
  $ L_1 (A,T) = "Ker" (K_1 (A[T]) -> K_1 (A)), $
  где гомоморфизм индуцирован пополнением $A[T] -> A$. Тогда порядок каждого
  элемента группы $L_1 (A,T)$ конечен и делит некоторую степень числа $N$.
] <prop:subdirect-polynomial-k-one-torsion>

#proof[
  Соображения индукции, использующие теоремы Гильберта о базисе и о сизигиях,
  позволяют свести нашу задачу к случаю, когда $T$ порождается одним образующим
  $t$. Записывая $s = t-1$, получаем, что $L_1 (A,T) = K_1 (A[s], s A[s])$. В
  силу @cor:graded-relative-k-one-unipotents, каждый элемент группы $L_1 (A,T)$
  обладает представителем вида $alpha = I+s v in GL_n (A[s])$, где $v$ —
  нильпотентная матрица над $A$. Пусть $R$ — подкольцо кольца
  $M_n (A[s]) = M_n (A)[s]$, порождённое $I$ и $alpha$. Тогда кольцо $R$ состоит
  из многочленов степени $<= d$ от $s v$ с целыми коэффициентами, где, скажем,
  $v^(d+1) = 0$. Применяя @prop:nilpotent-units-finiteness
  @cond:nilpotent-unit-exponent-bound к $R/(N^d R)$ и к идеалу, порождённому
  $s v$, получим, что $alpha^(N^r) = I mod N^d R$ для некоторого $r > 0$.
  Следовательно, можно записать
  $alpha^(N^r) = I+(alpha_1 s + dots + alpha_d s^d)N^d$, где каждый из элементов
  $alpha_i$ является целочисленным кратным элемента $v^i$.

  Положим $beta_i = N^(d-i) alpha_i$ $(1 <= i <= d)$ и
  $beta = alpha^(N^r) = I+beta_1 N s + dots + beta_d (N s)^d$. Пусть
  $gamma = I+beta_1 s + dots + beta_d s^d$. Очевидно, что $gamma$ — унипотентная
  матрица. Так как кольцо $B[s]$ регулярно справа, то из
  @cor:graded-relative-k-one-unipotents
  @cond:graded-relative-k-one-regular-vanishing следует, что
  $gamma in E (B[s], s B[s])$. Определим $f: B[s] -> B[s]$, полагая $f(b)=b$
  $(b in B)$ и $f(s)=N s$. Тогда $f(gamma)=beta$ и потому
  $beta in E (B[s], s N B[s])$. Но $s N B[s] subset A[s]$. Поэтому из
  @prop:subdirect-product-relative-k-one-excision вытекает, что
  $ E (B[s], s N B[s]) = E (A[s], s N B[s]). $
  Таким образом, $alpha^(N^r) = beta in E (A[s], s A[s])$, что и требовалось
  доказать.
]

В заключение этого параграфа применим предложение @prop:higman-linearization к
кольцу $A[t,t^(-1)]$. Формулировки результатов несколько более сложны, чем в
случае многочленов.

#source(496)#proposition[
  Каждый элемент $alpha in GL (A[t,t^(-1)])$ можно представить в виде
  #numbered-condition[
    $ alpha = tau_- epsilon_1 omega_- tau_+ alpha_0 omega_+ epsilon_2, $
  ] <eq:laurent-linear-factorization>
  где
  $ epsilon_i in E (A[t], (1-t)A[t]) quad (i=1,2), $
  $ alpha_0 in GL (A), $
  $ omega_± = I+(t^(±1)-1)v_±, $
  $v_±$ — нильпотентная матрица над $A$. Кроме того, $tau_+ = sigma_+ plus.o I$,
  а $tau_-$ — конечное произведение элементов вида $sigma_- plus.o I$, где
  матрицы $sigma_± in GL_n (A[t,t^(-1)])$ имеют вид
  $sigma_± = 1_(P_0[t,t^(-1)]) plus.o t^(±1) dot 1_(P_1[t,t^(-1)])$
  для некоторого разложения $A^n = P_0 plus.o P_1$. (Фактически
  $P_i = "Ker" (sigma_± - t^(±i) I_n) subset A^n$, $i=0,1$.) Кроме того, можно
  выбрать матрицу $tau_-$ диагональной и коммутирующей с $alpha$.
  #ed-note[
    В исходной формулировке $tau_-$ также имел вид одного элемента
    $sigma_- plus.o I$. Тогда все коэффициенты произведения в
    @eq:laurent-linear-factorization не содержат степеней $t$ ниже $-2$, что
    исключает, например, матрицу $(t^(-3))$ над полем. Конечное произведение
    таких элементов допускает множитель $t^(-N)I_m$, выбранный в доказательстве.
  ]
] <prop:laurent-linear-factorization>

#proof[
  Пусть $alpha in GL_m (A[t,t^(-1)])$. Тогда для достаточно большого числа $N$
  коэффициенты матрицы $t^N alpha$ — многочлены. Положим $tau_- = t^(-N) I_m$ и
  $s = 1-t$. Как и в @prop:higman-linearization, можем записать:
  $ epsilon_1^(-1) tau_-^(-1) alpha epsilon_2^(-1) = alpha_0 + alpha_1 s, $
  где, как и в @prop:higman-linearization, $epsilon_i in E (A[t], s A[t])$,
  $i=1,2$. Пополнение $A[t,t^(-1)] -> A$ $(s mapsto 0)$ переводит $alpha$ в
  $alpha_0 in GL (A)$. Поэтому #numbered-condition[
    $
      alpha = tau_- epsilon_1 beta alpha_0 epsilon_2,
      quad beta = I+gamma(t-1),
    $
  ] <eq:laurent-linear-first-reduction>
  где коэффициенты матрицы $gamma = -alpha_1 alpha_0^(-1)$ лежат в $A$.

  Для завершения доказательства покажем, что матрицу $beta$ можно записать в
  виде
  #numbered-condition[$ beta = omega_- tau_+ omega_+, $]
  <eq:laurent-linear-middle-factorization>
  где сомножители удовлетворяют условиям предложения. Тогда, используя
  @eq:laurent-linear-first-reduction, получим, что
  $ alpha = tau_- epsilon_1 omega_- tau_+ omega_+ alpha_0 epsilon_2. $
  Так как $alpha_0 in GL (A)$, то можем записать
  $omega_+ alpha_0 = alpha_0 omega_+^(alpha_0)$, где матрица $omega_+^(alpha_0)$
  того же типа, что и матрица $omega_+$. Следовательно, достаточно получить
  разложение @eq:laurent-linear-middle-factorization для $beta = I+gamma(t-1)$.

  Утверждаем, что $gamma^u (I-gamma)^v = 0$ для некоторых $u,v >= 0$.
  Действительно, матрица, обратная к матрице
  $beta = I+gamma(t-1) = delta+gamma t$ $(delta = I-gamma)$, имеет вид
  $beta^(-1) = sum gamma_i t^i in GL (A[t,t^(-1)])$. Таким образом,
  $ sum (delta gamma_i + gamma gamma_(i-1))t^i = I. $
  Тогда
  $ delta gamma_0 + gamma gamma_(-1) = I $
  #source(497)и
  $ delta gamma_i = -gamma gamma_(i-1), quad "если" i != 0. $
  Так как $delta$ и $gamma$ коммутируют, то из последних равенств вытекает, что
  для любых $u,v > 0$
  $
    delta^v gamma_(-1) = -delta^(v-1) gamma gamma_(-2)
    = (-1)^2 delta^(v-2) gamma^2 gamma_(-3)
    = dots = (-1)^v gamma^v gamma_(-(v+1)),
  $
  $
    gamma^u gamma_0 = -gamma^(u-1) delta gamma_1
    = (-1)^2 gamma^(u-2) delta^2 gamma_2
    = dots = (-1)^u delta^u gamma_u.
  $
  Для достаточно больших $u$ и $v$ получаем, что $gamma_(-(v+1)) = 0 = gamma_u$,
  поэтому $delta^v gamma_(-1) = 0 = gamma^u gamma_0$. Используя теперь равенство
  $delta gamma_0 + gamma gamma_(-1) = I$, получим, что
  $
    gamma^u delta^v = gamma^u delta^v (delta gamma_0 + gamma gamma_(-1))
    = delta^(v+1) gamma^u gamma_0 + gamma^(u+1) delta^v gamma_(-1) = 0.
  $

  Пусть $beta in GL_n (A[t,t^(-1)])$. Тогда $gamma in M_n (A)$. В подкольце
  кольца $M_n (A) = End_A (A^n)$, порождённом $gamma$, элементы $gamma^u$ и
  $(I-gamma)^v$ порождают всё кольцо. Так как $gamma^u (I-gamma)^v = 0$, то
  $A^n = P_0 plus.o P_1$, где $P_0 = "Ker" (gamma^u)$ и
  $P_1 = "Ker" ((I-gamma)^v)$. Запишем $J_i = 1_(P_i)$. Пусть $gamma_i$ —
  эндоморфизм модуля $P_i$, индуцированный при помощи $gamma$ $(i=0,1)$. Будем
  отождествлять $J_i$ и $gamma_i$ с их расширениями на $P_i[t,t^(-1)]$
  $(i=0,1)$. Тогда $beta = I_n + gamma(t-1) = beta_0 plus.o beta_1$, где
  $beta_i = J_i + gamma_i (t-1)$. Кроме того, $gamma_0$ и $J_1-gamma_1$
  нильпотентны. Пусть $beta'_0 = beta_0 plus.o J_1$ и
  $beta'_1 = J_0 plus.o beta_1$. Тогда
  $beta = beta'_0 beta'_1 = beta'_1 beta'_0$. Теперь положим
  $ omega_+ = beta'_0 = I_n + v_+(t-1), $
  где элемент $v_+ = gamma_0 plus.o 0$ нильпотентен. Разложение
  @eq:laurent-linear-middle-factorization мы получим, используя разложение
  $beta'_1$ в виде $omega_- tau_+$, как в
  @eq:laurent-linear-middle-factorization. Рассмотрим сначала $beta_1$. Имеем
  $
    beta_1 = J_1 + gamma_1 (t-1)
    = (gamma_1 + (J_1-gamma_1)t^(-1))(t J_1)
    = (J_1 + (J_1-gamma_1)(t^(-1)-1))(t J_1).
  $
  Следовательно, получаем нужное разложение для $beta'_1 = J_0 plus.o beta_1$
  при $tau_+ = J_0 plus.o t J_1$ и $omega_- = I_n + v_-(t^(-1)-1)$, где элемент
  $v_- = 0 plus.o (J_1-gamma_1)$ нильпотентен. Чем и завершается доказательство.
]

Замечание. Из результатов §~@sec:fundamental-theorem будет следовать, что
рассмотренное разложение @eq:laurent-linear-factorization обладает рядом сильных
свойств инвариантности.
