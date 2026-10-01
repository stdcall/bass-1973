#import "diagrams/stable-linear-groups-perfect-centralizer.typ": (
  diagram-perfect-centralizer,
)
#import "diagrams/stable-linear-groups-subgroup-level.typ": (
  diagram-subgroup-level,
)
#import "main-defs.typ": (
  Aff, E, GE, GL, SR, U, center, diag, source, symbol-idx, transpose,
)
#import "statements.typ": lemma, proof

#heading(level: 2)[Доказательство теоремы @th:linear-normal-subgroup-stability]
<sec:linear-stability-first-proof>

Сохраним предположения теоремы @th:linear-normal-subgroup-stability и
зафиксируем $m >= n$.

#proof(head: [Доказательство п.~@cond:linear-relative-elementary-normality.])[
  В силу @th:stable-rank-relative-elementary-stability
  @cond:stable-rank-elementary-transitivity из условия $SR_n (A, frak(q))$
  следует, что
  $GL_m (A, frak(q)) = E_m (A, frak(q)) dot GL_(n - 1) (A, frak(q))$. Допустим,
  что выполнено условие $SR_n (A)$. Мы собираемся показать, что
  $E_m (A, frak(q))$ — нормальный делитель группы $GL_m (A)$. В силу определения
  группа $E_m (A, frak(q))$ порождается элементами вида $tau^epsilon$, где
  $epsilon in E_m (A)$ и $tau = I_m + a e_(i j)$ $(a in frak(q), i != j)$. Так
  как все матрицы перестановки с определителем $1$ лежат в $E_m (A)$ (см.
  @cor:block-diagonal-elementary-congruences
  @cond:generalized-permutation-elementary-containment), то достаточно
  ограничиться рассмотрением $i = m$, и в этом случае матрица $tau$ имеет
  следующий вид: $tau = mat(I_(m - 1), 0; t, 1)$. Чтобы убедиться в том, что
  подгруппа $E_m (A, frak(q))$ является нормальным делителем группы $GL_m (A)$,
  достаточно показать, что $(tau^epsilon)^sigma in E_m (A, frak(q))$ для каждой
  матрицы $sigma in GL_m (A)$. Так как
  $(tau^epsilon)^sigma = (tau^(epsilon sigma epsilon^(-1)))^epsilon$ и так как
  матрица $epsilon in E_m (A)$ нормализует подгруппу $E_m (A, frak(q))$ (по
  определению), то достаточно, заменив $sigma$ на $epsilon sigma epsilon^(-1)$,
  показать, что $tau^sigma in E_m (A, frak(q))$. Запишем
  $sigma^(-1) = epsilon_0^(-1) (sigma')^(-1)$, где $epsilon_0 in E_m (A)$ и
  $sigma' = mat(sigma_1, 0; 0, 1) in GL_(m - 1) (A)$ (здесь использовано
  утверждение последнего абзаца). Тогда
  $tau^sigma = sigma^(-1) tau sigma = (tau^(sigma'))^(epsilon_0)$, и опять
  достаточно показать, что $tau^(sigma') in E_m (A, frak(q))$. Проведем
  вычисления и убедимся, #source(200)что
  $
    tau^(sigma') = mat(sigma_1^(-1), 0; 0, 1) mat(I, 0; t, 1)
    mat(sigma_1, 0; 0, 1) = mat(I, 0; t sigma_1, 1) in E_m (A, frak(q)),
  $ <eq:linear-lower-unipotent-conjugation>
  что и требовалось доказать.
]

#proof(head: [Доказательство п.~@cond:linear-relative-commutator-formulas.])[
  Допустим, что выполнено условие $SR_n (A, frak(q))$. Покажем, что
  $[GE_m (A), GL_m (A, frak(q))] subset E_m (A, frak(q))$. Из
  @cor:relative-elementary-commutators следует, что при $m >= 3$ имеет место
  равенство.

  Как и раньше, группа $E_m (A)$ порождается элементами вида $tau^epsilon$, где
  $epsilon in E_m (A)$ и $tau = mat(I, 0; t, 1)$. В силу
  @cor:block-diagonal-elementary-congruences
  @cond:relative-general-elementary-factorization группа $GE_m (A)$ порождается
  подгруппой $E_m (A)$ и элементами $delta = diag(1, dots, 1, u)$, где
  $u in U(A)$. Таким образом, достаточно показать, что
  $[sigma, delta tau^epsilon] in E_m (A, frak(q))$ для
  $sigma in GL_m (A, frak(q))$. Но
  $[sigma, delta tau^epsilon] = [sigma, tau^epsilon]
  [sigma, delta]^(tau^epsilon)$ и
  $[sigma, tau^epsilon] = [sigma^(epsilon^(-1)), tau]^epsilon$. Так как группа
  $E_m (A)$ нормализует $E_m (A, frak(q))$ (по определению), то достаточно
  показать, что элементы $[sigma, delta]$ и $[sigma, tau]$ лежат в
  $E_m (A, frak(q))$ для всех $sigma in GL_m (A, frak(q))$. В силу утверждения
  @cond:linear-relative-elementary-normality (примененного к $sigma^(-1)$),
  можно записать $sigma = sigma_1 epsilon_1$, где
  $sigma_1 = mat(sigma'_1, 0; 0, 1) in GL_(m - 1) (A, frak(q))$ и
  $epsilon_1 in E_m (A, frak(q))$. Тогда
  $[delta, sigma] = [delta, epsilon_1] [delta, sigma_1]^(epsilon_1)$. Так как
  $delta$ и $sigma_1$ перестановочны и так как $delta$ нормализует подгруппу
  $E_m (A, frak(q))$ (см.
  @cor:block-diagonal-elementary-congruences
  @cond:relative-general-elementary-factorization), то
  $[delta, sigma] in E_m (A, frak(q))$. Затем
  $[tau, sigma] = [tau, epsilon_1] [tau, sigma_1]^(epsilon_1)$, и поэтому
  остается показать, что $[tau, sigma_1] in E_m (A, frak(q))$. Но мы знаем (см.
  формулу @eq:linear-lower-unipotent-conjugation), что
  $
    [tau, sigma_1] = [mat(I, 0; t, 1), mat(sigma'_1, 0; 0, 1)]
    = mat(I, 0; t(sigma'_1 - I), 1) in E_m (A, frak(q)).
  $
  (Напомним, что $sigma'_1 equiv I mod frak(q)$.)

  Допустим, что выполнено условие $SR_n (A)$. Пусть $alpha in GL_m (A)$ и
  $beta in GL_m (A, frak(q))$. Тогда если $m >= 2(n - 1)$, то покажем, что
  $alpha$ и $beta$ перестановочны по модулю (нормального делителя)
  $E_m (A, frak(q))$. Действительно, как мы видели, элементы из $E_m (A)$
  перестановочны с $beta$ по модулю $E_m (A, frak(q))$. Можно считать, что
  $alpha = mat(alpha_0, 0; 0, I)$ по модулю $E_m (A)$, где
  $alpha_0 in GL_(n - 1) (A)$. Кроме того, можно считать, что
  $beta = mat(I, 0; 0, beta_0)$ по модулю $E_m (A, frak(q))$. В каждой из этих
  матриц $I = I_(m - (n - 1))$. Так как $m >= 2(n - 1)$, то из этого следует,
  что элементы $alpha$ и $beta$ теперь действительно перестановочны. Это
  показывает, что $[GL_m (A), GL_m (A, frak(q))] subset E_m (A, frak(q))$ для
  $m >= 2(n - 1)$.

  #source(201)Остается показать, что
  $[E_m (A), GL'_m (A, frak(q))] = E_m (A, frak(q))$ для $m >= n$ и $m >= 3$.
  Включение $supset$ следует из @cor:relative-elementary-commutators. Рассмотрим
  диаграмму подгрупп

  #diagram-subgroup-level()

  Учитывая все доказанное выше, мы видим, что справедливость обратного включения
  $subset$ вытекает из следующей леммы, примененной к группе
  $G = GL_m (A) slash E_m (A, frak(q))$:
]

#lemma[
  Рассмотрим диаграмму

  #diagram-perfect-centralizer()

  нормальных подгрупп группы $G$. Допустим, что $[E, C_1] subset C$,
  $[E, C] = {1}$ и $[E, E] = E$. Тогда $[E, C_1] = {1}$.
] <lem:perfect-normal-subgroup-centralizer>

#proof[
  Зафиксируем $gamma in C_1$ и определим отображение
  $
    h: E -> E inter C subset center(E),
  $
  полагая $h(epsilon) = [gamma, epsilon]$. Тогда
  $h(epsilon_1 epsilon_2) = [gamma, epsilon_1 epsilon_2]
  = [gamma, epsilon_2] [gamma, epsilon_1]^(epsilon_2)$
  (см. @ss:group-commutator-identities)
  $= [gamma, epsilon_2] [gamma, epsilon_1]$ (поскольку $[E, C] = {1}$)
  $= h(epsilon_1) h(epsilon_2)$ (поскольку группа $C inter E$ коммутативна).
  Таким образом, $h$ — гомоморфизм в абелеву группу. Так как $[E, E] = E$, то
  $[gamma, epsilon] = 1$ для всех $epsilon in E$. Таким образом,
  $[E, C_1] = {1}$, что и требовалось показать.
]

#proof(head: [Доказательство п.~@cond:linear-normalized-subgroup-level.])[
  Если для некоторого двустороннего идеала $frak(q)$ справедливы включения
  $E_m (A, frak(q)) subset H$ #source(202)$subset GL'_m (A, frak(q))$ и если
  $m >= max(n, 3)$, то из @cond:linear-relative-commutator-formulas вытекает,
  что
  $
    E_m (A, frak(q)) = [E_m (A), E_m (A, frak(q))] subset [E_m (A), H]
    subset [E_m (A), GL'_m (A, frak(q))] = E_m (A, frak(q)),
  $
  и, следовательно, $E_m (A)$ нормализует подгруппу $H$.

  Предположим теперь обратное, т.~е. что $H subset GL_m (A)$ является
  подгруппой, которую нормализует группа $E_m (A)$, и что $m >= max(n, 3)$. Нам
  надо показать, что подгруппа $H$ имеет указанный вид.
]

#lemma[
  Если $H$ не лежит в центре, то $E_m (A, frak(q)) subset H$ для некоторого
  ненулевого двустороннего идеала $frak(q)$.
] <lem:noncentral-elementary-normalized-subgroup>

Закончим сначала, используя утверждение леммы, доказательство теоремы. Пусть
$frak(q)$ — наибольший двусторонний идеал, такой, что
$E_m (A, frak(q)) subset H$ (очевидно, он существует). Мы должны показать, что
образ $H'$ группы $H$ в $GL_m (A')$ (где $A' = A slash frak(q)$) лежит в центре
последней. В силу @prop:stable-rank-ideals-quotients @cond:stable-rank-quotient
из предположения $SR_n (A)$ теоремы @th:linear-normal-subgroup-stability
вытекает справедливость условия $SR_n (A')$. Кроме того, $H'$ нормализуется
образом группы $E_m (A)$, совпадающим в силу
@prop:elementary-matrices-quotient-surjection с $E_m (A')$. Следовательно, если
$H'$ не лежит в центре, то из леммы
@lem:noncentral-elementary-normalized-subgroup вытекает, что $H'$ содержит
$E_m (A', frak(q)' slash frak(q))$ для некоторого двустороннего идеала
$frak(q)' != frak(q)$. Переходя к полному прообразу, получаем, что
$E_m (A, frak(q)') subset GL_m (A, frak(q)) dot H$. Предположим, что
$epsilon in E_m (A)$, $alpha in H$ и $beta in GL_m (A, frak(q))$. Тогда
$[epsilon, beta alpha] = [epsilon, alpha] [epsilon, beta]^alpha$. Так как
$E_m (A)$ нормализует подгруппу $H$, то $[epsilon, alpha] in H$. Кроме того, из
@cond:linear-relative-commutator-formulas вытекает, что
$[epsilon, beta] in E_m (A, frak(q)) subset H$. Таким образом,
$[epsilon, beta alpha] in H$. Следовательно,
$
  E_m (A, frak(q)') = [E_m (A), E_m (A, frak(q)')]
  subset [E_m (A), GL_m (A, frak(q)) dot H] subset H.
$
Но это противоречит максимальности идеала $frak(q)$. Итак, доказательство
п.~@cond:linear-normalized-subgroup-level завершено, если будет проведено

#proof(head: [Доказательство леммы
  @lem:noncentral-elementary-normalized-subgroup.])[
  _Случай 1._ Группа $H$ содержит нецентральный элемент $sigma = u alpha$, где
  $u$ — обратимый центральный элемент и
  $
    alpha = mat(1, 0; x, alpha_0) in Aff_(m - 1) (A)
    = mat(1, 0; A^(m - 1), GL_(m - 1) (A)).
  $
  Через $A^(m - 1)$ обозначим множество матриц вида $tau(t) = mat(1, 0; t, I)$
  $(t in A^(m - 1))$. Достаточно показать, что $H inter A^(m - 1) != {I}$.
  Действительно, тогда из @prop:affine-subgroup-commutators
  @cond:affine-invariant-ideals следует, что $H$ содержит все матрицы $tau(t)$,
  у которых элементы строчки $t$ лежат в некотором левом идеале $frak(a) != 0$.
  Тогда из @cor:elementary-level-containment вытекает, что $H$ содержит
  $E_m (A, frak(a) A)$. Но
  $[tau(t), sigma] = [tau(t), alpha] = tau((alpha_0^(-1) - I) t)$, и поэтому все
  будет доказано, если $alpha_0 != I$. В противном случае, поскольку элемент
  $sigma$ #source(203)не лежит в центре, $x != 0$, поэтому найдется матрица
  $epsilon = mat(1, 0; 0, epsilon_0) in E_m (A)$, такая, что
  $epsilon_0 (x) != x$. Таким образом, группа $H$ содержит
  $[sigma, epsilon] = [alpha, epsilon] = [tau(x), epsilon]
  = tau((epsilon_0^(-1) - I)(x)) != I$ в $A^(m - 1)$.

  _Случай 2._ Группа $H$ содержит нецентральный элемент $sigma$, у которого по
  крайней мере один элемент вне диагонали равен нулю.

  Сопрягая при помощи элемента группы $E_m (A)$, можно считать, что нулевой
  элемент находится в первой строке $alpha = (a_1, dots, a_m)$ матрицы $sigma$ и
  даже что $a_m = 0$. Если $t in A$, то положим $tau(t) = I + t e_(2 1)$. Тогда
  $sigma^(-1) tau(t) sigma = I + beta t alpha$, где $beta = #transpose(
    $(b_1, dots, b_m)$,
    mark: $T$,
  )$ — второй столбец матрицы $sigma^(-1)$. («$T$» означает
  транспонирование.)#symbol-idx(
    $T$,
    sort: "superscript T",
    group: "superscripts",
    order: 152,
  ) Предположим, что $sigma$ коммутирует со всеми матрицами $tau(t)$. Полагая
  $t = 1$, получим, что $alpha = (u, 0, dots, 0)$ и $beta = #transpose(
    $(0, u^(-1), 0, dots, 0)$,
    mark: $T$,
  )$. Кроме того, $u^(-1) t u = t$ для всех $t$, так что $u$ — обратимый
  центральный элемент кольца $A$, т.~е. мы находимся в ситуации случая 1.

  Таким образом, можно считать, что существует элемент $tau = tau(t)$, такой,
  что $gamma = [tau, sigma] != I$, $gamma = tau^(-1) + tau^(-1) beta t alpha$.
  Так как $a_m = 0$, то последний столбец матрицы $tau^(-1) beta t alpha$
  нулевой, и поэтому $gamma = mat(gamma_0, 0; x, 1)$. В частности, $gamma$ не
  лежит в центре. Кроме того, матрица
  $#transpose($gamma$, mark: $T$)
  = mat(#transpose($gamma_0$, mark: $T$), #transpose($x$, mark: $T$); 0, 1)$
  принадлежит множеству $E_m (A)$-сопряженных с матрицами из $Aff_(m - 1) (A)$
  матриц, и поэтому закончить доказательство можно так же, как в случае 1.

  _Общий случай._ Выберем нецентральный элемент $sigma$ в $H$. Пусть
  $alpha = #transpose($(a_1, dots, a_m)$, mark: $T$)$ — первый столбец матрицы
  $sigma$. Если $epsilon = I + sum_(1 <= i < m) b_i e_(i m)$, то первый столбец
  матрицы $epsilon sigma epsilon^(-1)$ совпадает с $#transpose(
    $(a_1 + b_1 a_m, dots, a_(m - 1) + b_(m - 1) a_m, a_m)$,
    mark: $T$,
  )$. В силу условия $SR_n (A)$, следовательно, можно считать, сопрягая при
  помощи элемента из $E_m (A)$, что строка $(a_1, dots, a_(m - 1))$
  унимодулярна. Тогда можно записать $a_m = sum_i s_i a_i$ $(1 <= i < m)$.
  Полагая $epsilon = I - sum_(1 <= i < m) s_i e_(m i)$, получаем, что
  $epsilon alpha = #transpose($(a_1, dots, a_(m - 1), 0)$, mark: $T$)$.

  Пусть $tau = I + t e_(1 2)$. Рассмотрим
  $delta = sigma tau sigma^(-1) tau^(-1) = (I + alpha t beta) tau^(-1)$, где
  $beta$ — вторая строка матрицы $sigma^(-1)$. Как и в случае 2, можно выбрать
  элемент $t$ так, что $delta != I$, или же мы возвращаемся к случаю 2.

  Положим теперь $sigma' = epsilon delta epsilon^(-1)
  = epsilon tau^(-1) epsilon^(-1) + epsilon alpha t beta epsilon^(-1)$. Так как
  последняя координата строки $epsilon alpha$ равна нулю, то нижняя строка
  матрицы $(epsilon alpha)(t beta epsilon^(-1))$ нулевая. Следовательно, у
  матриц $sigma'$ и
  $epsilon tau^(-1) epsilon^(-1) = I - epsilon t e_(1 2) epsilon^(-1)$
  совпадают нижние строки. Но
  $
    epsilon t e_(1 2) epsilon^(-1)
    #source(204)= (I - sum_(i < m) s_i e_(m i)) t e_(1 2)
    (I + sum_(i < m) s_i e_(m i))
    = (t e_(1 2) - s_1 t e_(m 2))(I + sum_(i < m) s_i e_(m i))
    = t e_(1 2) - s_1 t e_(m 2)
  $
  (напомним, что $m >= 3$). Следовательно, последняя строка матрицы $sigma'$
  равна $(0, s_1 t, 0, dots, 0, 1)$. Так как $sigma'$ не равна $I$, то она не
  может лежать в центре (один из ее диагональных элементов равен $1$), и мы
  можем применить метод случая 2 к элементу $sigma' in H$.

  Этим заканчивается доказательство леммы
  @lem:noncentral-elementary-normalized-subgroup и, следовательно, теоремы
  @th:linear-normal-subgroup-stability.
]
