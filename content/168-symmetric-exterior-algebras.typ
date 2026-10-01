#import "main-defs.typ": (
  Aut, Coker, Im, K, Ker, U, idx, moduleCategory, name-idx, ob, source,
  symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, example, numbered-condition, proof,
  proposition,
)
#import "diagrams/projective-k-theory-exterior.typ": (
  exterior-koszul-complex, exterior-operation-naturality,
)

== Приложение: симметрическая алгебра обратна к внешней алгебре
<sec:symmetric-exterior-algebras>

Если $A$ — кольцо и $t$ — переменная, то определим для $M in A-moduleCategory$
$ M[[t]] = {"формальные степенные ряды" sum_(i >= 0) m_i t^i} quad (m_i in M). $
#symbol-idx($M[[t]]$, sort: "M[[t]]", group: "groups", order: 111)
Получаем левый модуль над кольцом степенных рядов $A[[t]]$. «Постоянный член» —
это гомоморфизм $A[[t]] -> A$. Введем еще одно обозначение:
$ U_1 (A[[t]]) = Ker(U(A[[t]]) -> U(A)). $
Если $F in A[[t]]$, то элемент $1 - t F$ обратим, а его обратный равен
$sum_(n >= 0) t^n F^n$. Отсюда следует, что $U_1 (A[[t]]) = 1 + t A[[t]]$.

Начиная с этого момента, мы зафиксируем коммутативное кольцо $A$. Пусть нам дан
(неаддитивный) функтор $L = L_A$ из категории $A$-модулей в категорию
градуированных $A$-модулей
$ P -> L(P) = (L^n (P))_(n >= 0), $
удовлетворяющий следующим условиям:
#condition-list[
  #condition-item(format: "(1°)")[$L^0$ является постоянным функтором $P |-> A$.
    Если $P in bold(P)(A)$, то $L^n (P) in bold(P)(A)$ для всех
    $n >= 0$.] <cond:graded-operation-projective-values>
  #condition-item(format: "(1°)")[Существует естественный изоморфизм
    $ L(P plus.o Q) tilde.eq L(P) tensor_A L(Q). $
    (Здесь мы рассматриваем тензорное произведение градуированных модулей, и
    поэтому изоморфизм состоит из совокупности изоморфизмов
    $ L^n (P plus.o Q) tilde.eq union.sq.big_(i+j=n) L^i (P) tensor_A L^j (Q) $
    для всех $n >= 0$.)] <cond:graded-operation-direct-sum>
  #condition-item(format: "(1°)")[Если $A -> B$ — гомоморфизм коммутативных
    колец, то существует естественный изоморфизм градуированных $B$-модулей
    $ L_A (P) tensor_A B tilde.eq L_B (P tensor_A B), $
    т. е. «функтор $L$ перестановочен с заменой колец».]
  <cond:graded-operation-base-change>
]

#source(400)Имея такой функтор, можно определить
$ L: K_0 (A) -> U_1 (K_0 (A)[[t]]), $
полагая
$ L[P] = sum_(n >= 0) [L^n P] t^n quad (P in bold(P)(A)). $
Свойство @cond:graded-operation-projective-values показывает, что элемент правой
части лежит в $U_1 (K_0 (A)[[t]])$. Из свойства
@cond:graded-operation-direct-sum следует, что мы получаем аддитивную функцию из
$ob bold(P)(A)$ в абелевы группы. Следовательно, $L$ является корректно
определенным гомоморфизмом #numbered-condition[$
  L(x + y) = L(x) L(y).
$] <eq:graded-operation-k0-additivity>
Кроме того, свойство @cond:graded-operation-base-change показывает, что этот
гомоморфизм естественный в том смысле, что диаграмма
$ #exterior-operation-naturality() $
коммутативна для гомоморфизма $A -> B$ из @cond:graded-operation-base-change.

Далее предположим, что $(P, alpha) in Sigma bold(P)(A)$, т. е. что
$P in bold(P)(A)$ и $alpha in Aut_A (P)$. Тогда можно определить
$ L: ob Sigma bold(P)(A) -> K_1 (A)[[t]], $
полагая
$ L(P, alpha) = sum_(n >= 0) [L^n P, L^n alpha] t^n. $
(Заметим, что $[L^0 P, L^0 alpha] = [A, 1_A] = 0$ в силу
@cond:graded-operation-projective-values.) Если также $beta in Aut_A (P)$, то
$L^n (alpha beta) = L^n (alpha) L^n (beta)$ (так как $L$ является функтором).
Поэтому #numbered-condition[
  $
    L(P, alpha beta) = L(P, alpha) + L(P, beta) quad (P in bold(P)(A); alpha,
      beta in Aut_A (P)).
  $
] <eq:graded-operation-k1-composition>
Если $(P, alpha)$ и $(Q, beta)$ — объекты категории $Sigma bold(P)(A)$, то
$
  L(P plus.o Q, alpha plus.o beta) = sum_(n >= 0) [union.sq.big_(i+j=n) (L^i P
      tensor_A L^j Q, L^i alpha tensor L^j beta)] t^n.
$
Так как
$
  [L^i P tensor L^j Q, L^i alpha tensor L^j beta] =
  [L^i P tensor L^j Q, 1_(L^i P) tensor L^j beta] +
  [L^i P tensor L^j Q, L^i alpha tensor 1_(L^j Q)] =
  [L^i P] [L^j Q, L^j beta] + [L^j Q] [L^i P, L^i alpha]
$
(мы используем структуру $K_0 (A)$-модуля на $K_1 (A)$), то из приведенной выше
формулы следует, что #numbered-condition[
  $ L(P plus.o Q, alpha plus.o beta) = L[P] L(Q, beta) + L[Q] L(P, alpha). $
] <eq:graded-operation-k1-direct-sum>

#source(401)Это подсказывает введение функции
$ L_1 (P, alpha) = L[P]^(-1) L(P, alpha). $
Но тогда из @eq:graded-operation-k1-composition вытекает, что функтор $L_1$ все
еще аддитивен относительно композиции. Кроме того, сопоставляя
@eq:graded-operation-k1-direct-sum и @eq:graded-operation-k0-additivity,
получаем
$
  L_1 (P plus.o Q, alpha plus.o beta) =
  L[P plus.o Q]^(-1) L(P plus.o Q, alpha plus.o beta) =
  L[P]^(-1) L[Q]^(-1) (L[P] L(Q, beta) + L[Q] L(P, alpha)) =
  L_1 (P, alpha) + L_1 (Q, beta).
$
Таким образом, видим, что $L_1$ индуцирует аддитивный гомоморфизм
$ L_1: K_1 (A) -> K_1 (A)[[t]]. $
Так же как и для функторов $L$ и $K_0$, проверяется, что это — естественное
преобразование.

#example[
  Пусть $L_A = Lambda_A$ — внешняя алгебра.#symbol-idx(
    $Lambda$,
    sort: "∧",
    group: "symbols",
    order: 142,
  ) Справедливость условий
  @cond:graded-operation-projective-values–@cond:graded-operation-base-change
  хорошо известна. Функтор $Lambda^1$ является тождественным функтором, и
  $Lambda^n (A) = 0$ для $n > 1$. Поэтому $Lambda[A] = 1 + t$. Следовательно,
  $Lambda[A^n] = (1 + t)^n$.

  Если $u in U(A)$, то обозначим $[u] = [A, u] in K_1 (A)$. Тогда
  $Lambda(A, u) = [u] t$. Поэтому
  $ L_1 [u] = (1 + t)^(-1) [u] t = [u](t - t^2 + t^3 - dots.c). $
] <exm:exterior-power-k-operations>

#example[
  Пусть $L_A = S_A$ — симметрическая алгебра. Выполнение условий
  @cond:graded-operation-projective-values–@cond:graded-operation-base-change
  также хорошо известно. При этом $S^1$ — тождественный функтор, и
  $S^n (A) tilde.eq A$ для всех $n >= 0$. Поэтому
  $S[A] = sum_(n >= 0) t^n = (1 - t)^(-1)$. Таким образом,
  $ S[A](t) = Lambda[A](-t)^(-1). $
  Обобщение этого утверждения будет приведено ниже (предложение
  @prop:symmetric-exterior-operation-inversion).

  Если $u in U(A)$, то
  $
    S_1 [u] = (1 - t) (sum_(n >= 0) [u^n] t^n) = sum_(n > 0) ([u^n] - [u^(n-1)])
    t^n = sum_(n > 0) [u] t^n = [u] (sum_(n > 0) t^n).
  $
] <exm:symmetric-power-k-operations>

Пусть $P$ — любой $A$-модуль и $d: P -> A$ — линейный функционал. Тогда $d$
продолжается до дифференцирования алгебры $Lambda(P)$ следующим образом:
#numbered-condition[
  $
    d(x_1 and dots.c and x_n) = sum_(1 <= i <= n) (-1)^(i-1) d(x_i) (x_1 and
      dots.c hat(x_i) dots.c and x_n).
  $
] <eq:koszul-differential>
#source(402)Это определяет положительный комплекс, так называемый «комплекс
Кошуля»#idx("комплекс Кошуля"): #numbered-condition[$
  #exterior-koszul-complex()
$] <eq:koszul-complex>
группа гомологии которого с нулевым номером равна $Coker(d) = A slash frak(a)$,
где $frak(a) = Im(P arrow.r^d A)$. Имеется следующий хорошо известный критерий
обращения в нуль других групп гомологии (см., например, книгу Серра#name-idx(
  "Серр (Serre J.-P.)",
) @bib:Serre1965, главу 4, ч. А), который мы приведем без доказательства.

#proposition[
  Пусть $P = A^n$ с базисом $(e_i)$ $(1 <= i <= n)$ и пусть отображение
  $d: P -> A$ определено значениями $d(e_i) = a_i$. Положим
  $frak(a)_i = sum_(1 <= j < i) A a_j$. Допустим, что образ элемента $a_i$ в
  $A slash frak(a)_i$ не является делителем нуля $(1 <= i <= n)$. Тогда комплекс
  @eq:koszul-complex является свободной резольвентой модуля
  $A slash frak(a)_(n+1)$.
] <prop:koszul-regular-sequence-resolution>

Это предложение используется в основном тогда, когда $A$ — кольцо многочленов,
т. е. $A = B[a_1, dots, a_n] tilde.eq S_B (B^n)$.

Применим предложение @prop:koszul-regular-sequence-resolution в следующей
ситуации. Пусть $P$ является $A$-модулем. Тогда $P = S^1 (P) subset S(P)$.
Поэтому это вложение индуцирует $S(P)$-линейное отображение
$ d: S(P) tensor_A P -> S(P). $
Как и выше, оно продолжается до дифференцирования внешней алгебры
$Lambda_(S(P)) (S(P) tensor_A P)$, нулевая группа гомологии которого равна
$ A = S(P) slash T, $
где $T$ — идеал, порожденный $P = S^1 (P)$. Если модуль $P$ — свободный с
базисом $(e_i)$ $(1 <= i <= n)$, то $S(P)$ является кольцом многочленов
$A[e_1, dots, e_n]$. Кроме того, $S(P) tensor_A P$ — свободный $S(P)$-модуль с
базисом $(1 tensor e_i)$ $(1 <= i <= n)$, и $d(1 tensor e_i) = e_i$. Таким
образом, из @prop:koszul-regular-sequence-resolution следует, что
$Lambda_(S(P)) (S(P) tensor_A P)$ является проективной резольвентой для $A$ в
этом случае. Более общим образом, если $P in bold(P)(A)$, то можно применить
последнее утверждение ко всем локализациям
$P_(frak(m)) in bold(P)(A_(frak(m)))$, являющимся свободными модулями, и
показать, что комплекс $Lambda_(S(P)) (S(P) tensor_A P)$ ацикличен всюду, кроме
нулевой степени.

Заметим, что $Lambda_(S(P)) (S(P) tensor_A P) = S(P) tensor_A Lambda_A (P)$.
Поэтому комплекс биградуирован с помощью $S^n (P) tensor_A Lambda^m (P)$
$(n, m >= 0)$. Кроме того, так как $d$ продолжается по $S(P)$-линейности, то,
рассматривая вложение $P = S^1 (P) subset S(P)$, можно #source(403)показать, что
с учетом @eq:koszul-differential отображение $d$ индуцирует гомоморфизмы
$ S^n (P) tensor_A Lambda^m (P) -> S^(n+1) (P) tensor_A Lambda^(m-1) (P). $
Это показывает, что $Lambda_(S(P)) (S(P) tensor_A P)$ как комплекс $A$-модулей
разлагается в прямую сумму подкомплексов вида #numbered-condition[
  $
    0 -> S^0 (P) tensor_A Lambda^n (P) -> S^1 (P) tensor_A Lambda^(n-1) (P) ->
    dots -> S^n (P) tensor_A Lambda^0 (P) -> 0,
  $
] <eq:homogeneous-koszul-complex>
по одному для каждого $n >= 0$. Как мы видели выше, если $P in bold(P)(A)$, то
комплекс @eq:homogeneous-koszul-complex ацикличен всюду, кроме одного члена
комплекса при $n = 0$:
$ 0 -> S^0 (P) tensor_A Lambda^0 (P) -> 0. $
В этом случае, следовательно,
$ sum_(0 <= i <= n) (-1)^i [S^i (P)] [Lambda^(n-i) (P)] = 0 "в группе" K_0 (A) $
для всех $n > 0$. Это доказывает следующую элегантную формулу:

#proposition[
  Пусть $Lambda, S: K_0 (A) -> U_1 (K_0 (A)[[t]])$ — отображения,
  соответствующие внешней алгебре (см. @exm:exterior-power-k-operations) и
  симметрической алгебре (см. @exm:symmetric-power-k-operations) соответственно.
  Тогда если $x in K_0 (A)$, то
  $ Lambda(x)(t) dot S(x)(-t) = 1. $
] <prop:symmetric-exterior-operation-inversion>
