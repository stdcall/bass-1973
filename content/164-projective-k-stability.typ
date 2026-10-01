#import "main-defs.typ": (
  G, H, Hom, Homology, K, Ker, Pic, Rk, codim, dim, ed-note, idx, maxSpec,
  moduleCategory, rad, rk, source, supp, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, proof, proposition,
)

== Теоремы о стабильности <sec:projective-k-stability>

В этом параграфе мы _зафиксируем коммутативное кольцо $R$_. Пусть
$ X = maxSpec(R). $
Под носителем $R$-модуля $M$ понимается его носитель в $X$:
$ supp_m (M) = {frak(m) in X | M_frak(m) != 0}. $

#proposition[
  Пусть $X$ — нётерово пространство, являющееся объединением конечного числа
  подпространств размерности $<= d$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Если $u in K_0 (R)$ и его ранг $>= d$,
      то $u = [P]$ для некоторого модуля $P in bold(P)(R)$.]
    <cond:k0-large-rank-effective>
    #condition-item(format: "cyrillic")[Если $P, Q in bold(P)(R)$ и
      $[P: R] > d$, то из равенства $[P] = [Q]$ следует, что $P approx Q$.]
    <cond:k0-large-rank-cancellation>
  ]
] <prop:k0-large-rank-stability>

#proof[
  @cond:k0-large-rank-effective Можно записать $u = [Q] - [R^n]$ для некоторого
  модуля $Q in bold(P)(R)$. Так как $[Q: R] = n + rk(u)$ #source(366)$>= n + d$,
  то из теоремы Серра @cor:serre-free-summand следует, что
  $Q approx P plus.o R^n$ для некоторого $P$, и поэтому $u = [P]$.

  @cond:k0-large-rank-cancellation Если $[P] = [Q]$, то
  $P plus.o R^n approx Q plus.o R^n$ для некоторого $n$. Если $[P: R] > d$, то
  из теоремы о сокращении @cor:projective-cancellation следует, что
  $P approx Q$.
]

Аналогичный результат мы получаем без предположений о конечности.

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Если ранг элемента $u in K_0 (R)$ всюду
      положителен, то $n u = [P]$ для некоторого $n > 0$ и некоторого
      $P in bold(P)(R)$.] <cond:k0-positive-rank-multiple-effective>
    #condition-item(format: "cyrillic")[Если $P, Q in bold(P)(R)$ и $[P] = [Q]$,
      то $P^n approx Q^n$ для некоторого $n > 0$.]
    <cond:k0-equal-class-multiple-isomorphism>
  ]
] <prop:k0-multiple-stability>
#ed-note[
  Неотрицательности ранга недостаточно. Пусть $R = {f in QQ[t] | f(0) = f(1)}$ и
  $M = {f in QQ[t] | f(1) = 2 f(0)}$. Из последовательности
  @th:projective-k-mayer-vietoris для квадрата с кольцами $QQ[t]$, $QQ$ и
  $QQ times QQ$ следует, что $Pic(R) tilde.eq QQ^*$, причем классу $M$
  соответствует $2$. Элемент $u = [M] - [R]$ имеет ранг нуль и бесконечный
  порядок: его определитель соответствует $2$. Если бы $n u = [P]$ при $n > 0$,
  то $P$ имел бы ранг нуль, откуда $P = 0$ и $2^n = 1$, что невозможно.
]


#proof[
  @cond:k0-positive-rank-multiple-effective Пусть $u = [P] - [R^m]$. Тогда
  модуль $P$ определен над конечно порожденным подкольцом $R_0 subset R$, и
  кольцо $R_0$ нётерово. Кроме того, $u$ является образом элемента
  $u_0 = [P_0] - [R_0^m]$, где модуль $P_0 in bold(P)(R_0)$ такой, что
  $P_0 tensor_(R_0) R approx P$. Для достаточно больших $n$ ранг элемента
  $n u_0$ превосходит $dim maxSpec(R_0)$. Поэтому из
  @prop:k0-large-rank-stability @cond:k0-large-rank-effective следует, что
  $n u_0 = [Q_0]$ для некоторого $Q_0$. Таким образом,
  $n u = [Q_0 tensor_(R_0) R]$.

  @cond:k0-equal-class-multiple-isomorphism Предположим, что $[P] = [Q]$.
  Ограничивая кольцо $R$ его прямым слагаемым, можно считать, что модуль $P$
  точный. Кроме того, существует изоморфизм $h: P plus.o R^m -> Q plus.o R^m$
  для некоторого $m$. Можно теперь выбрать $R_0 subset R$ достаточно большим и
  так, что найдутся $P_0, Q_0 in bold(P)(R_0)$ и
  $h_0: P_0 plus.o R_0^m -> Q_0 plus.o R_0^m$, для которых
  $P = P_0 tensor_(R_0) R$, $Q = Q_0 tensor_(R_0) R$ и $h = h_0 tensor_(R_0) R$.
  В частности, $[P_0] = [Q_0]$ в группе $K_0 (R_0)$, поэтому $[P_0^n] = [Q_0^n]$
  для всех $n > 0$. Если число $n$ настолько большое, что
  $[P_0^n: R_0] > dim maxSpec(R_0)$, то можно применить предложение
  @prop:k0-large-rank-stability @cond:k0-large-rank-cancellation и показать, что
  $P_0^n approx Q_0^n$. Следовательно, $P^n approx Q^n$. Доказательство
  закончено.
]

Пусть $A$ есть $R$-алгебра. Введем на группе $K_0 (A)$ фильтрацию, из свойств
которой будут выведены некоторые полезные утверждения.

Пусть $C = (dots C_n arrow.r^(d_n) C_(n-1) dots)$ и
$C' = (dots C'_n arrow.r^(d'_n) C'_(n-1) dots)$ — комплексы в категориях
$moduleCategory-A$ и $moduleCategory-B$ соответственно, где $A$ и $B$ суть
$R$-алгебры. Тогда можно определить комплекс $C tensor_R C'$ в категории
$moduleCategory-(A tensor_R B)$ следующим образом:
$ (C tensor_R C')_n = union.sq.big_(i+j=n) C_i tensor C'_j. $
Если $a in C_i$ и $a' in C'_j$, то
$D(a tensor a') = d a tensor a' + (-1)^i a tensor d' a'$. Предположим, что
комплекс $C$ стягиваем, т. е. существует морфизм $s: C -> C$ степени единица,
для которого $s d + d s = 1_C$. Тогда #source(367)если $S = s tensor 1_(C')$,
$D S + S D = 1_(C tensor_R C')$. Поэтому комплекс $C tensor_R C'$ также
стягиваем. Действительно, пусть элемент $a tensor a'$ выбран, как и выше. Тогда
$
  D S(a tensor a') = D(s a tensor a')
  = d s a tensor a' + (-1)^(i+1) s a tensor d' a'
  = (a - s d a) tensor a' + (-1)^(i+1) s a tensor d' a'
  = a tensor a' - S(d a tensor a' + (-1)^i a tensor d' a')
  = (a tensor a') - S D(a tensor a').
$
Если $P$ — конечный комплекс в категории $bold(P)(A)$, то положим
$ chi(P) = chi^A (P) = sum_n (-1)^n [P_n] in K_0 (A). $
Если комплекс $P$ ацикличен, то $chi(P) = 0$ (см.
@prop:euler-characteristic-identities @cond:euler-homology-invariance). Если
$A -> B$ — гомоморфизм алгебр, то отображение $K_0 (A) -> K_0 (B)$ переводит
элемент $chi^A (P)$ в $chi^B (P tensor_A B)$. Если $Q$ — конечный комплекс в
категории $bold(P)(B)$, то спаривание
$K_0 (A) tensor_(K_0 (R)) K_0 (B) -> K_0 (A tensor_R B)$ переводит элемент
$chi^A (P) tensor chi^B (Q)$ в $chi^(A tensor_R B) (P tensor_R Q)$.

Напомним (см. @prop:closed-support-finite-complex), что носитель комплекса
гомологий $Homology(P)$ конечного комплекса $P in bold(P)(A)$ замкнут:
$ supp_m (Homology(P)) subset X = maxSpec(R). $
Поскольку локализация — точный функтор, она перестановочна с функтором
гомологии. Кроме того, если конечный комплекс в категории $bold(P)(A)$
ацикличен, то он стягиваем (см. @cor:acyclic-projective-contractible). Таким
образом,
$
  supp_m (Homology(P)) = {frak(m) in X | Homology(P)_frak(m) != 0}
  = {frak(m) in X | Homology(P_frak(m)) != 0}
  = {frak(m) in X | P_frak(m) "не ацикличен"}
  = {frak(m) in X | P_frak(m) "не стягиваем"}.
$
Если $Q$ — конечный комплекс в категории $bold(P)(B)$, то
$(P tensor_R Q)_frak(m) = P_frak(m) tensor_(R_frak(m)) Q_frak(m)$. Как мы видели
выше, тензорное произведение стягиваемо, если один из сомножителей стягиваем.
Таким образом, получаем включение
$
  supp_m (Homology(P tensor_R Q)) subset supp_m (Homology(P))
  inter supp_m (Homology(Q)).
$

#definition(title: [групп $F^i K_0 (A)$])[
  Если $i >= 0$, то через $F^i K_0 (A)$ обозначим множество элементов
  $u in K_0 (A)$, удовлетворяющих следующему условию: для заданного замкнутого
  множества $Y subset X$ существует конечный комплекс $P$ в категории
  $bold(P)(A)$, для которого $chi(P) = u$ и
  $ codim_Y (Y inter supp_m (Homology(P))) >= i. $
] <def:k0-support-filtration>

#source(368)#proposition[
  #condition-list[
    #condition-item[$F^i K_0 (A)$ образуют убывающую цепь подгрупп, при этом
      $F^0 K_0 (A) = K_0 (A)$ и $F^i K_0 (A) = 0$, если $i > dim X$.]
    <cond:k0-support-filtration-decreasing>
    #condition-item[Если $B$ — другая $R$-алгебра, то естественное спаривание
      $K_0 (A) tensor_(K_0 (R)) K_0 (B) -> K_0 (A tensor_R B)$ индуцирует
      гомоморфизмы
      $F^i K_0 (A) tensor F^j K_0 (B) -> F^(i+j) K_0 (A tensor_R B)$ для всех
      $i, j >= 0$. В частности, таким образом кольцо $K_0 (R)$ превращается в
      фильтрованное кольцо, а $K_0 (A)$ — в фильтрованный $K_0 (R)$-модуль.]
    <cond:k0-support-filtration-multiplicative>
    #condition-item[Гомоморфизм $R$-алгебр $A -> B$ индуцирует гомоморфизмы
      $F^i K_0 (A) -> F^i K_0 (B)$ для всех $i >= 0$.]
    <cond:k0-support-filtration-natural>
    #condition-item[Если $A$ — конечномерная $R$-алгебра и пространство $X$
      нётерово, то
      $
        F^1 K_0 (A) = inter.big_(frak(m) in X) Ker(K_0 (A) -> K_0 (A_frak(m))).
      $
      В частности, $F^1 K_0 (R) = Rk_0 (R)$ и $(Rk_0 (R))^(d+1) = 0$, где
      $d = dim X$.] <cond:k0-support-filtration-rank-kernel>
  ]
] <prop:k0-support-filtration-properties>

#proof[
  @cond:k0-support-filtration-decreasing Пусть $u, v in F^i K_0 (A)$. Покажем,
  что $u + v in F^i K_0 (A)$. Для этого пусть $Y$ — замкнутое подмножество в
  $X$. Если $P$ и $Q$ — конечные комплексы в категории $bold(P)(A)$, возникающие
  в определении @def:k0-support-filtration для элементов $u$ и $v$
  соответственно, то комплекс $P plus.o Q$ играет соответствующую роль для
  элемента $u + v$, а комплекс $P(-1)$ (где $P(-1)_n = P_(n-1)$) — для элемента
  $-u$. Последнее утверждение очевидно, поскольку
  $Homology(P(-1)) = Homology(P)(-1)$. Первое вытекает из равенства
  $
    supp_m (Homology(P) plus.o Homology(Q)) = supp_m (Homology(P))
    union supp_m (Homology(Q))
  $
  и того замечания, что коразмерность объединения двух замкнутых множеств равна
  минимуму из двух коразмерностей. Очевидно, что фильтрация убывающая. Если
  $u in F^i K_0 (A)$ и $i > dim X$, то можно выбрать $P$ так, что $u = chi(P)$ и
  $codim_X (X inter supp_m (Homology(P))) >= i > dim X$. Таким образом,
  $Homology(P) = 0$, т. е. комплекс $P$ ацикличен. Следовательно,
  $u = chi(P) = 0$.

  @cond:k0-support-filtration-multiplicative Пусть $u in F^i K_0 (A)$,
  $v in F^j K_0 (B)$, $w$ — образ элемента $u tensor v$ в группе
  $K_0 (A tensor_R B)$. Нам надо показать, что
  $w in F^(i+j) K_0 (A tensor_R B)$. Поэтому пусть нам дано замкнутое множество
  $Y subset X$. Выберем конечный комплекс $P$ в категории $bold(P)(A)$, для
  которого $chi^A (P) = u$ и $codim_Y (Z) >= i$, где
  $Z = Y inter supp_m (Homology(P))$. Выберем теперь конечный комплекс $Q$ в
  категории $bold(P)(B)$ так, что $chi^B (Q) = v$ и
  $codim_Z (Z inter supp(Homology(Q))) >= j$. Покажем, что конечный комплекс
  $P tensor_R Q$ категории $bold(P)(A tensor_R B)$ удовлетворяет условиям из
  @def:k0-support-filtration для $w$ и $Y$. Очевидно, что элемент
  $chi^(A tensor_R B) (P tensor_R Q)$ является образом элемента
  $chi^A (P) tensor chi^B (Q) = u tensor v$ и, следовательно, равен элементу
  $w$. Кроме того, как мы видели выше,
  $
    supp_m (Homology(P tensor_R Q)) subset supp_m (Homology(P))
    inter supp_m (Homology(Q)).
  $
  #source(369)Следовательно,
  $
    codim_Y (Y inter supp_m (Homology(P tensor_R Q)))
    >= codim_Y (Y inter supp_m (Homology(P)) inter supp_m (Homology(Q)))
    = codim_Y (Z inter supp_m (Homology(Q)))
    >= codim_Y (Z) + codim_Z (Z inter supp_m (Homology(Q)))
    >= i + j.
  $

  @cond:k0-support-filtration-natural Пусть $A -> B$ — гомоморфизм $R$-алгебр и
  $u in F^i K_0 (A)$. Пусть нам дано замкнутое множество $Y$ в $X$. Выберем
  комплекс $P$ для элемента $u$ (как в @def:k0-support-filtration). Тогда
  $supp_m (Homology(P tensor_A B)) subset supp_m (Homology(P))$ (это
  показывается аналогично с использованием локальной стягиваемости комплексов
  $P_frak(m)$ для $frak(m) in.not supp_m (Homology(P))$). Образ $v$ элемента $u$
  в группе $K_0 (B)$, очевидно, равен $chi^B (P tensor_A B)$. Поэтому
  $v in F^i K_0 (B)$.

  @cond:k0-support-filtration-rank-kernel Пусть $u in F^1 K_0 (A)$ и
  $frak(m) in X$. Тогда можно найти комплекс $P$, для которого
  $
    chi(P) = u "и" codim_{frak(m)} ({frak(m)} inter supp_m (Homology(P))) >= 1.
  $
  Из последнего условия вытекает, что $frak(m) in.not supp_m (Homology(P))$.
  Поэтому комплекс $P_frak(m)$ ацикличен и, следовательно, элемент $u$
  отображается в нуль группы $K_0 (A_frak(m))$.

  Обратно, пусть
  $u in inter.big_(frak(m) in X) Ker(K_0 (A) -> K_0 (A_frak(m)))$. Покажем, что
  $u in F^1 K_0 (A)$. Поэтому пусть нам дано замкнутое множество $Y$ в $X$. Так
  как пространство $X$ предполагается нётеровым, можно записать $Y$ в виде
  несократимого объединения неприводимых замкнутых подмножеств, скажем
  $Y_1, dots, Y_n$. Выберем различные элементы $frak(m)_i in Y_i$
  ($1 <= i <= n$). Если $u = [P] - [Q]$, то в силу предположения
  $[P_(frak(m)_i)] = [Q_(frak(m)_i)]$ в группе $K_0 (A_(frak(m)_i))$ для каждого
  $i$. Добавляя большой свободный модуль к $P$ и $Q$, можно даже считать, что
  $P_(frak(m)_i) approx Q_(frak(m)_i)$ для каждого $i$. Так как
  $Hom_(A_(frak(m)_i)) (P_(frak(m)_i), Q_(frak(m)_i))
  = Hom_A (P, Q)_(frak(m)_i)$, то можно найти $h^i: P -> Q$, для которого
  $h^i_(frak(m)_i)$ является изоморфизмом ($1 <= i <= n$). Так как идеалы
  $frak(m)_i$ комаксимальны, то в силу китайской теоремы об остатках существует
  $h in Hom_A (P, Q)$, для которого $h - h^i in frak(m)_i dot Hom_A (P, Q)$
  ($1 <= i <= n$). Локально имеем
  $frak(m)_i A_(frak(m)_i) subset rad A_(frak(m)_i)$, поскольку $A$ —
  конечномерная $R$-алгебра. Следовательно, из леммы Накаямы (см.
  @prop:nakayama-lemma) получаем, что $h_(frak(m)_i)$ — изоморфизм, поскольку
  отображение $h_(frak(m)_i)$ конгруэнтно изоморфизму $h^i_(frak(m)_i)$ по
  модулю $rad A_(frak(m)_i)$. Таким образом, комплекс
  $ C = (dots 0 -> P arrow.r^h Q -> 0 dots), $
  #source(370)где $P = C_0$, ацикличен для каждого $frak(m)_i$. Очевидно, что
  $chi(C) = u$. Так как $Z = Y inter supp(Homology(C))$ не содержит по крайней
  мере одной точки $frak(m)_i$ из каждой неприводимой компоненты $Y_i$
  пространства $Y$, то $codim_Y (Z) >= 1$.

  Ясно, что
  $Rk_0 (R) = inter.big_(frak(m) in X) Ker(K_0 (R) -> K_0 (R_frak(m)))$.
  Следовательно, из @cond:k0-support-filtration-decreasing и
  @cond:k0-support-filtration-multiplicative вытекает, что
  $Rk_0 (R)^n subset F^n K_0 (R) = 0$, если $n > dim X$. Доказательство
  закончено.
]

#corollary[
  Пусть $X$ — нётерово пространство размерности $<= d$, $P in bold(P)(R)$ —
  точный модуль и $n$ — наименьшее общее кратное его локальных рангов. Тогда
  существует модуль $Q in bold(P)(R)$, для которого
  $P tensor_R Q approx R^(n^(d+1))$.
] <cor:projective-free-tensor-complement-bound>

#proof[
  Если $n = 1$, то $P$ — обратимый модуль и можно взять $Q = P^*$, поскольку
  $P tensor_R P^* approx R$. Пусть теперь $n >= 2$. Очевидно, что можно найти
  элемент $r in H_0 (R)$, для которого $r [P: R] = n$. Пусть $[P] = [P: R] - t$
  в разложении $K_0 (R) = H_0 (R) plus.o Rk_0 (R)$. Тогда $r [P] = n - r t$.
  Таким образом, по модулю главного идеала $[P] K_0 (R)$ $n equiv r t$ и
  $(r t)^(d+1) = 0$ в силу части @cond:k0-support-filtration-rank-kernel
  предложения @prop:k0-support-filtration-properties. Из этого следует, что
  $n^(d+1) in [P] K_0 (R)$. Пусть $n^(d+1) = [P] u$. Тогда ранг элемента $u$ не
  меньше, чем $n^d$, но $n^d > d$. Поэтому из @prop:k0-large-rank-stability
  @cond:k0-large-rank-effective следует, что $u = [Q]$ для некоторого модуля
  $Q$. Так как $[P tensor_R Q] = n^(d+1) = [R^(n^(d+1))]$ и $n^(d+1) > d$, то из
  @prop:k0-large-rank-stability @cond:k0-large-rank-cancellation получаем, что
  $P tensor_R Q approx R^(n^(d+1))$.
]

Не делая предположения о конечности, получаем такое утверждение:

#proposition[
  $Rk_0 (R)$ является нильидеалом. Если $P in bold(P)(R)$, то следующие условия
  эквивалентны:
  #condition-list[
    #condition-item[модуль $P$ точный (и, следовательно, строго проективный в
      смысле гл.~@ch:module-categories,
      §~@sec:module-category-characterization);]
    <cond:projective-free-tensor-faithful>
    #condition-item[функция $[P: R]$ всюду положительна;]
    <cond:projective-free-tensor-positive-rank>
    #condition-item[каждый $K_0 (R)$-модуль, аннулируемый элементом $[P]$,
      является периодическим;] <cond:projective-free-tensor-torsion-annihilator>
    #condition-item[существуют модуль $Q in bold(P)(R)$ и число $n > 0$, для
      которых $P tensor Q approx R^n$.] <cond:projective-free-tensor-complement>
  ]
] <prop:strict-projective-free-tensor-complement>

#proof[
  Так как $K_0 (R)$ является прямым пределом групп $K_0 (R')$, где $R'$
  пробегает конечно порожденные подкольца кольца $R$ и, следовательно, нётеровы
  кольца, то утверждение о том, что $Rk_0 (R)$ — нильидеал, следует из
  соответствующего свойства каждого из идеалов $Rk_0 (R')$ (см.
  @prop:k0-support-filtration-properties
  @cond:k0-support-filtration-rank-kernel). Эквивалентность условий
  @cond:projective-free-tensor-faithful и
  @cond:projective-free-tensor-positive-rank вытекает из
  @prop:projective-rank-formulas. Если функция $[P: R]$ всюду положительна, то,
  как и в доказательстве следствия @cor:projective-free-tensor-complement-bound,
  можно найти решение неравенства $r [P: R] = n > 0$ в группе $H_0 (R)$. Тогда
  $r [P] = n - s$ для $s in Rk_0 (R)$. Так как $s^d = 0$ для некоторого $d > 0$,
  то $n^d in [P] K_0 (R)$, откуда вытекает
  @cond:projective-free-tensor-torsion-annihilator.

  #source(371)Далее, из @cond:projective-free-tensor-torsion-annihilator
  следует, что $t [P] = n$ для некоторого $n > 0$ (надо применить
  @cond:projective-free-tensor-torsion-annihilator к
  $K_0 (R) slash ([P] K_0 (R))$). Выбирая $n$ достаточно большим, если это
  необходимо, можно считать, что ранг элемента $t$ достаточно большой. Тогда
  некоторое кратное элемента $t$ в силу @prop:k0-multiple-stability
  @cond:k0-positive-rank-multiple-effective имеет вид $[Q]$. Таким образом, еще
  раз увеличивая $n$, можно считать, что $[Q] [P] = n$ для некоторого
  $Q in bold(P)(R)$. Так как $[Q tensor_R P] = [R^n]$, то из
  @prop:k0-multiple-stability @cond:k0-equal-class-multiple-isomorphism следует,
  что
  $ (Q tensor_R P)^m = Q^m tensor_R P approx (R^n)^m = R^(n m) $
  для некоторого $m > 0$. Это доказывает
  @cond:projective-free-tensor-complement.

  Импликация @cond:projective-free-tensor-complement $=>$
  @cond:projective-free-tensor-faithful очевидна. Тем самым предложение
  доказано.
]

#corollary(title: [«критерий периодичности»])[
  #idx("критерий периодичности")Пусть $R -> L$ — мономорфизм коммутативных
  колец, для которого $L in bold(P)(R)$. Пусть $A$ — $R$-алгебра. Тогда группы
  $ Ker(K_i (A) -> K_i (L tensor_R A)) quad (i = 0, 1) $
  и
  $ Ker(G_i (A) -> G_i (L tensor_R A)) quad (i = 0, 1) $
  периодические. Если пространство $maxSpec(R)$ нётерово и его размерность
  $<= d$, то эти группы аннулируются числом $n^(d+1)$, где $n$ — наименьшее
  общее кратное локальных рангов $R$-модуля $L$.
] <cor:projective-k-torsion-kernels>

#proof[
  В силу @prop:projective-k-transfer-scalar-multiplication существует
  гомоморфизм
  $ K_i (L tensor_R A) -> K_i (A), $
  композиция которого с отображением $K_i (A) -> K_i (L tensor_R A)$ дает
  умножение на элемент $[L]_R in K_0 (R)$ в группе $K_i (A)$ ($i = 0, 1$).
  Аналогичное утверждение получаем и для функторов $G_i$ ($i = 0, 1$). Тогда все
  рассматриваемые ядра аннулируются элементом $[L]_R$. Таким образом,
  утверждение следствия вытекает из
  @prop:strict-projective-free-tensor-complement
  @cond:projective-free-tensor-torsion-annihilator и из
  @cor:projective-free-tensor-complement-bound соответственно.
]
