#import "main-defs.typ": Hom, Ker, idx, source
#import "statements.typ": corollary, proof, proposition, theorem
#import "diagrams/vector-bundles-projective-modules-sections.typ": (
  section-map-lift,
)

== Расслоения на нормальном пространстве имеют достаточно много сечений
<sec:normal-space-bundle-sections>

Элементы множества $Gamma(E)$ для $E in bold(italic(B))(X)$ мы будем называть
_глобальными сечениями_. Они определяют аддитивный функтор
$ Gamma:bold(italic(B))(X)->k(X)"-"italic("mod"). $
#idx("глобальное сечение")
Покажем, что если $X$ — нормальное пространство, то этот функтор вполне строгий.

_Всюду в этом параграфе $X$ — нормальное пространство._ Это означает, что если
$U$ — окрестность точки $x in X$, то существует непрерывная функция $f$ из $X$ в
единичный отрезок, которая равна нулю вне некоторой замкнутой окрестности точки
$x$, содержащейся в $U$, и принимает значение $1$ в некоторой (более малой)
окрестности точки $x$. #idx("нормальное пространство")

Пусть $E in bold(italic(B))(X)$ и $s in Gamma(E, U)$. Тогда если определить
$s'$, полагая $s'(x)=f(x)s(x)$ для $x in U$ и $s'(x)=0$ для $x in.not U$, то
легко заметить, что $s' in Gamma(E)$ и $s'=s$ в окрестности точки $x$. Таким
образом, получаем

#proposition[
  Если $E in bold(italic(B))(X)$ и $s$ — локальное сечение расслоения $E$ в
  окрестности точки $x$, то существует сечение $s' in Gamma(E)$, для которого
  $s'$ и $s$ совпадают в окрестности точки $x$.
] <prop:normal-space-global-section-extension>

#corollary[
  Если $x in X$, то существуют глобальные сечения расслоения $E$, образующие
  локальный базис для расслоения $E$ в точке $x$.
] <cor:normal-space-global-local-basis>

#source(557)
#corollary[
  Если $f,g:E->E'$ — морфизмы из категории $bold(italic(B))(X)$ и
  $Gamma(f)=Gamma(g)$, то $f=g$.
] <cor:global-sections-faithful>

#proof[
  Если $e in E_x$, то выберем $s in Gamma(E)$ так, чтобы $s(x)=e$. Такое сечение
  существует локально, а значит, в силу
  @prop:normal-space-global-section-extension глобально. Тогда
  $f(e)=f s(x)=Gamma(f)(s)(x)=Gamma(g)(s)(x)=g s(x)=g(e)$, что и требовалось
  доказать.
]

Если $x in X$, то получаем гомоморфизм колец
$ phi_x:k(X)->k, quad phi_x (f)=f(x). $
Положим $frak(m)_x=Ker(phi_x)$ (это максимальный идеал в кольце $k(X)$).

#proposition[
  Гомоморфизм $Gamma(E)->E_x$, при котором $s mapsto s(x)$, индуцирует
  изоморфизм
  $ Gamma(E) slash (frak(m)_x Gamma(E))->E_x. $
] <prop:bundle-fiber-section-quotient>

#proof[
  Сюръективность этого отображения следует из
  @prop:normal-space-global-section-extension. При этом очевидно, что
  гомоморфизм аннулирует $frak(m)_x Gamma(E)$. Остается показать, что если
  $s(x)=0$, то $s in frak(m)_x Gamma(E)$. Выберем $s_1,dots,s_n in Gamma(E)$,
  образующие локальный базис в точке $x$ (см.
  @cor:normal-space-global-local-basis). Тогда для подходящих функций
  $b_i in k(X)$ сечения $sum b_i s_i$ и $s$ совпадают в окрестности точки $x$.
  (Сначала мы подберем $b_i$ локально в точке $x$, а затем глобально, как в
  @prop:normal-space-global-section-extension.) Так как
  $0=s(x)=sum b_i (x)s_i (x)$, то $b_i (x)=0$, т. е. $b_i in frak(m)_x$
  ($1<=i<=n$). Положим $s'=s-sum b_i s_i$. Тогда $s'$ обращается в нуль в
  некоторой окрестности $U$ точки $x$. Выберем функцию $r in k(X)$ так, чтобы
  $r=1$ вне $U$ и $r=0$ в некоторой окрестности точки $x$. Тогда
  $r in frak(m)_x$ и $s'=r s'$. Поэтому
  $ s=s'+sum b_i s_i=r s'+sum b_i s_i in frak(m)_x Gamma(E), $
  что и требовалось доказать.
]

#theorem[
  Функтор
  $ Gamma:bold(italic(B))(X)->k(X)"-"italic("mod") $
  вполне строгий.
] <th:normal-space-global-sections-fully-faithful>

#proof[
  Утверждается, что
  $ Gamma:Hom_(bold(italic(B))(X)) (E,E')->Hom_(k(X)) (Gamma(E),Gamma(E')) $
  — изоморфизм для $E,E' in bold(italic(B))(X)$. Инъективность этого отображения
  вытекает из следствия @cor:global-sections-faithful.
  #source(558)
  Пусть $overline(f):Gamma(E)->Gamma(E')$ является $k(X)$-гомоморфизмом.
  Используя @prop:bundle-fiber-section-quotient, определим
  $overline(f)_x:E_x->E'_x$ из коммутативной диаграммы:
  #section-map-lift()
  Отображения $overline(f)_x$ задают отображение множеств $f:E->E'$ над $X$,
  которое линейно на каждом слое ($f_x=overline(f)_x$). Если $s in Gamma(E)$, то
  $(f s)(x)=overline(f)_x (s(x))=overline(f)(s)(x)$. Поэтому
  $ f s=overline(f)(s) quad (s in Gamma(E)). $ <eq:bundle-section-map-lift>
  Это показывает, что $f$ переводит глобальные сечения в глобальные сечения. В
  силу @prop:normal-space-global-section-extension локальные сечения переходят в
  локальные сечения. Следовательно, из @cor:bundle-map-continuity-from-sections
  следует, что $f$ является морфизмом расслоений, а @eq:bundle-section-map-lift
  утверждает, что $Gamma(f)=overline(f)$, что и требовалось доказать.
]
