#import "main-defs.typ": *
#import "statements.typ": *

== Теоремы Герстена и Столлингса о свободных произведениях
<sec:gersten-stallings-free-products>

В этом параграфе через $R$ обозначим коммутативное кольцо. Рассмотрим
пополненную $R$-алгебру $A$ (см. @ch:stable-projective-structure,
§~@sec:free-products-firs-cohns-theorem). Таким образом, получаем точную
последовательность
$ 0 -> overline(A) -> A arrow.r^(epsilon_A) R -> 0, $
которая расщепляется как последовательность $R$-модулей (здесь $epsilon_A$ —
пополнение, а $overline(A)$ — идеал пополнения). Если $F$ — любой функтор из
категории колец в категорию абелевых групп, то
$F(A)=F(R) plus.o overline(F)(A)$, где $overline(F)(A)=Ker(F(A) -> F(R))$.

Если $B$ — другая пополненная $R$-алгебра, то через $A ast_R B$ мы обозначим
копроизведение (или свободное произведение) алгебр $A$ и $B$ (см.
@ch:stable-projective-structure, §~@sec:free-products-firs-cohns-theorem). Если
$M in moduleCategoryOf(R)$, то через $T_R (M)$ обозначим тензорную алгебру
модуля $M$.

#theorem(title: "Столлингс")[
  #idx("теорема Столлингса")Пусть $A$ и $B$ — пополненные $R$-алгебры. Тогда
  имеет место точная последовательность
  $
    overline(K)_1 (T_R (overline(A) tensor_R overline(B)))
    -> overline(K)_1 (A ast_R B) -> overline(K)_1 (A) plus.o overline(K)_1 (B)
    -> 0,
  $
  расщепляющаяся справа.
] <th:stallings-free-product-k-one>

#proof[
  Пусть $C=A ast_R B$. Рассмотрим естественные гомоморфизмы пополненных алгебр
  $A -> C -> A$ и $B -> C -> B$, композиции которых являются соответствующими
  тождественными отображениями. Так как при отображении $C -> A$ идеал
  пополнения $overline(B)$ переходит в нуль, а при отображении $C -> B$ идеал
  пополнения $overline(A)$ переходит в нуль, то из формальных соображений
  следует, что
  $
    overline(K)_1 (C) approx overline(K)_1 (A) plus.o overline(K)_1 (B)
    plus.o (?).
  $
  Но
  $overline(K)_1 (C)=K_1 (C,overline(C))=GL(C, overline(C))/E(C,overline(C))$.
  Так как $R$-алгебра $C$ порождается множеством
  $overline(A) plus.o overline(B)$, а последнее множество порождает
  $overline(C)$, то из @prop:higman-linearization следует, что любой элемент
  группы $overline(K)_1 (C)$ представим матрицей вида $gamma=I+alpha+beta$, где
  элементы матрицы $alpha$ лежат в $overline(A)$, а элементы матрицы $beta$
  лежат в $overline(B)$. Отображение #source(528)$C -> B$ переводит $alpha$ в
  нуль, а отображение $C -> A$ переводит $beta$ в нуль. Таким образом,
  $I+alpha in GL(A, overline(A))$ и $I+beta in GL(B, overline(B))$.

  Положим $I+delta=(I+alpha)^(-1)(I+alpha+beta)(I+beta)^(-1)$. Тогда элемент
  $ (I+alpha)(I+delta)=I+delta+alpha(I+delta) $
  равен элементу
  $ (I+alpha+beta)(I+beta)^(-1)=I+alpha(I+beta)^(-1). $
  Поэтому матрица $alpha$ является левым множителем матрицы $delta$. Аналогично
  матрица $beta$ является правым множителем матрицы $delta$. Поэтому элементы
  матрицы $delta$ лежат в $overline(A)overline(B)$
  $(=overline(A) tensor_R overline(B))$ в $C$. Используя описание алгебры $C$,
  данное в (@ch:stable-projective-structure,
  §~@sec:free-products-firs-cohns-theorem), получаем, что гомоморфизм
  $T_R (overline(A) tensor_R overline(B)) -> C$, индуцированный вложением
  $overline(A)overline(B) subset C$, является мономорфизмом. Этот гомоморфизм
  индуцирует отображение
  $
    f: overline(K)_1 (T_R (overline(A) tensor_R overline(B)))
    -> overline(K)_1 (C),
  $
  в образе которого лежит класс рассмотренного выше элемента $I+delta$. Так как
  элемент $gamma$ (с которого мы начали наше рассуждение) является произведением
  $gamma=(I+alpha)(I+delta)(I+beta)$, то класс элемента $gamma$ лежит в
  $overline(K)_1 (A) plus.o Im(f) plus.o overline(K)_1 (B)$. Это завершает
  доказательство теоремы @th:stallings-free-product-k-one.#name-idx(
    "Столлингс (Stallings J.)",
  )
]

#corollary[
  Если кольцо $R$ регулярно и если $R$-модуль $overline(A) tensor_R overline(B)$
  свободен, то отображение
  $ overline(K)_1 (A ast_R B) -> overline(K)_1 (A) plus.o overline(K)_1 (B) $
  является изоморфизмом.
] <cor:regular-free-product-k-one>

#proof[
  В этом случае $T_R (overline(A) tensor_R overline(B))$ — кольцо многочленов от
  некоммутирующих переменных над кольцом $R$. Из теоремы Герстена
  (@cor:gersten-tensor-algebra-k-one) следует, что
  $overline(K)_1 (T_R (overline(A) tensor_R overline(B)))=0$, если кольцо $R$
  регулярно. Таким образом, следствие вытекает из этой теоремы.
]

#corollary(title: "Герстен")[
  #idx("теорема Герстена")В предположениях следствия
  @cor:regular-free-product-k-one естественный гомоморфизм
  $ overline(K)_0 (A ast_R B) -> overline(K)_0 (A) plus.o overline(K)_0 (B) $
  оказывается изоморфизмом.
] <cor:gersten-free-product-k-zero>

#proof[
  Пусть $(T,T_±)$ — ориентированный цикл. Рассмотрим замену колец
  $R subset R[T_±] subset R[T]$. Далее, через
  $ f_i (R): K_i (A) plus.o K_i (B) -> K_i (A ast_R B) quad (i=0,1) $
  обозначим естественные гомоморфизмы (индуцированные включениями
  $A subset A ast_R B supset B$). В силу формальных рассуждений (см.
  доказательство теоремы @th:stallings-free-product-k-one)
  $K_i (A ast_R B)=K_i (R)$ #source(529)$plus.o overline(K)_i (A)
  plus.o overline(K)_i (B) plus.o (?)$. Поэтому следствие, утверждающее, что
  группа $(?)$ равна нулю, будет доказано, как только мы убедимся в том, что
  отображение $f_0 (R)$ сюръективно. Из @cor:regular-free-product-k-one мы
  знаем, что отображение $f_1 (R)$ сюръективно, если кольцо $R$ регулярно. Но
  кольца $R[T_±]$ и $R[T]$ регулярны по теореме Гильберта о сизигиях
  (@th:swan-polynomial-regularity), а копроизведение пополненных алгебр
  коммутирует с заменой колец. Применяя основную теорему
  @th:fundamental-k-theory-laurent, получим стягиваемую точную
  последовательность морфизмов
  $
    0 -> f_1 (R) -> f_1 (R[T_+]) plus.o f_1 (R[T_-])
    -> f_1 (R[T]) -> f_0 (R) -> 0.
  $
  Так как все отображения $f_1$ в последовательности сюръективны (как это было
  отмечено выше), то получаем, что и отображение $f_0 (R)$ сюръективно, что и
  требовалось доказать.
]

Замечание. Результаты для функтора $NilGroup$, аналогичные следствию
@cor:gersten-free-product-k-zero для функтора $K_0$, могут быть получены
подобными рассуждениями.
