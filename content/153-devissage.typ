#import "main-defs.typ": Aut, End, Ex, GL, Im, Int, K, U, idx, maxSpec, source
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, proof, proposition,
  theorem,
)
#import "diagrams/abelian-k-theory-exact.typ": devissage-composition-square

== Редукция «отвинчиванием» <sec:devissage>
#idx("отщипывание")#idx("редукция отщипыванием")

Пусть $bold(C)_0 subset bold(C)$ — допустимая подкатегория абелевой категории.
Вложение является точным функтором, который, поэтому индуцирует гомоморфизмы
$ K_i (bold(C)_0) -> K_i (bold(C)) quad (i=0,1). $
В этом и в следующем параграфах мы выясним, когда эти гомоморфизмы являются
изоморфизмами. Достаточное условие для #source(316)этого, грубо говоря,
заключается в наличии у любого объекта категории $bold(C)$ «хорошего
композиционного ряда» с факторами из подкатегории $bold(C)_0$. Более точно:

#definition(word: [Определения])[
  _$bold(C)_0$-фильтрацией_#idx("C_0-фильтрация") объекта $A$ категории
  $bold(C)$ называется конечная фильтрация вида
  $0=A_0 subset A_1 subset dots subset A_n=A$, где
  $A_i slash A_(i-1) in bold(C)_0$ ($1 <= i <= n$). Будем говорить, что эта
  фильтрация _стабильна_#idx("C_0-фильтрация стабильная") при действии
  автоморфизма $alpha in Aut_(bold(C)) (A)$, если $alpha A_i=A_i$
  ($0 <= i <= n$). Назовем такую фильтрацию _характеристической_,#idx(
    "C_0-фильтрация характеристическая",
  ) если она стабильна при всех таких $alpha$. Автоморфизм
  $alpha in Aut_(bold(C)) (A)$ назовем _$bold(C)_0$-унипотентным_,#idx(
    "C_0-унипотентный автоморфизм",
  ) если найдется указанная выше $bold(C)_0$-фильтрация, для которой
  $(1_A-alpha)A_i subset A_(i-1)$ ($1 <= i <= n$). Это означает, что фильтрация
  стабильна при действии $alpha$ и что $alpha$ индуцирует тождественное
  отображение на каждом факторе $A_i slash A_(i-1)$. Из этого, очевидно,
  следует, что автоморфизм $alpha$ _унипотентный_,#idx(
    "унипотентный автоморфизм",
  ) т. е. что эндоморфизм $1_A-alpha$ нильпотентен.
] <def:devissage-filtrations>

#proposition[
  Пусть $A$ — объект категории $bold(C)$ и $alpha in Aut_(bold(C)) (A)$. Тогда:
  #condition-list(start: 0)[
    #condition-item[Если $0=A_0 subset A_1 subset dots subset A_n=A$ — конечная
      $bold(C)$-фильтрация, то все $A_i in bold(C)$ и
      $[A]=sum_i [A_i slash A_(i-1)]$ ($1 <= i <= n$) в группе
      $K_0 (bold(C))$.] <cond:filtration-k0-additivity>

    #condition-item[Если автоморфизм $alpha$ $bold(C)$-унипотентен, то $alpha$ —
      унипотентный элемент. Обратное утверждение верно, если категория $bold(C)$
      абелева, и в этом случае $[A,alpha]=0$ в группе $K_1 (bold(C))$ для
      $bold(C)$-унипотентного элемента $alpha$.] <cond:unipotent-k1-vanishing>
  ]
] <prop:filtration-additivity-unipotence>

#proof[
  @cond:filtration-k0-additivity Проведем индукцию по $n$. Случай $n=1$
  тривиален. Если $n>1$, то из рассмотрения последовательности
  $ 0 -> A_(n-1) -> A_n -> A_n slash A_(n-1) -> 0 $
  следует, что $A_(n-1) in bold(C)$ (условие @cond:admissible-kernel-closure из
  @def:admissible-abelian-subcategory). Таким образом, используя индуктивное
  предположение, получим, что
  $
    [A]=[A_(n-1)]+[A_n slash A_(n-1)]=sum_i [A_i slash A_(i-1)] quad (1 <= i <=
      n).
  $

  @cond:unipotent-k1-vanishing Первая часть утверждения была отмечена выше.
  Обратно, пусть эндоморфизм $f=1_A-alpha$ нильпотентен, скажем $f^n=0$. Пусть
  $A_i=Im (f^(n-i))$ ($0 <= i <= n$). Если категория $bold(C)$ абелева, то
  получаем $bold(C)$-фильтрацию, относительно которой $alpha$ является
  $bold(C)$-унипотентным автоморфизмом.

  Если автоморфизм $alpha$ $bold(C)$-унипотентный, то выберем
  $bold(C)$-фильтрацию, как выше, так что $(alpha-1_A)A_i subset A_(i-1)$
  ($1 <= i <= n$). Тогда $alpha$ индуцирует отображение $1_(B_i)$ на
  $B_i=A_i slash A_(i-1)$. Из части @cond:filtration-k0-additivity следует (в
  применении к категории $Sigma bold(C)$), что $[A,alpha]=sum_i [B_i,1_(B_i)]$
  ($1 <= i <= n$), поэтому и $[A,alpha]=0$.
]

#source(317)
#theorem[
  Пусть $bold(C)_0 subset bold(C)$ — допустимая подкатегория абелевой категории.
  Допустим, что все факторобъекты объектов из $bold(C)_0$ лежат в $bold(C)_0$.
  Тогда:
  #condition-list(start: 0)[
    #condition-item[если каждый объект $A in bold(C)$ обладает
      $bold(C)_0$-фильтрацией, то отображение
      $K_0 (bold(C)_0) arrow.r^(j_0) K_0 (bold(C))$ — изоморфизм;]
    <cond:devissage-k0-isomorphism>

    #condition-item[если каждый объект $A in bold(C)$ обладает
      характеристической $bold(C)_0$-фильтрацией, то отображение
      $K_1 (bold(C)_0) arrow.r^(j_1) K_1 (bold(C))$ — изоморфизм.]
    <cond:characteristic-devissage-k1-isomorphism>
  ]
] <th:devissage-k-isomorphisms>

#proof[
  @cond:devissage-k0-isomorphism Из предположений о подкатегории $bold(C)_0$
  следует, что подразбиение $bold(C)_0$-фильтрации опять является
  $bold(C)_0$-фильтрацией. В силу леммы Цассенхауза @prop:zassenhaus-refinement
  любые две конечные фильтрации обладают такими продолжениями, что факторы
  первого продолжения изоморфны факторам второго продолжения (с точностью до
  перестановки в порядке следования). Это показывает, что если
  $0=A_0 subset A_1 subset dots subset A_n=A$ — любая $bold(C)_0$-фильтрация
  объекта $A in bold(C)$, то элемент
  $J(A)=sum_i [A_i slash A_(i-1)]_(bold(C)_0)$ ($1 <= i <= n$) определен
  корректно. В силу сделанных замечаний надо лишь проверить, что $J(A)$ не
  меняется при замене данной фильтрации ее продолжением. Это равносильно
  введению фильтрации в каждом из факторов $A_i slash A_(i-1)$. Поэтому желаемое
  утверждение следует из части @cond:filtration-k0-additivity предложения
  @prop:filtration-additivity-unipotence (в применении к категории $bold(C)_0$).

  Если $(0 -> A' -> A -> A'' -> 0) in Ex (bold(C))$, то можно ввести
  $bold(C)_0$-фильтрацию в объекте $A$ начиная с фильтрации для $A'$ и продолжая
  ее затем полным прообразом фильтрации объекта $A''$. При таком выборе
  фильтрации мы видим, что $J(A)=J(A')+J(A'')$. Отсюда следует, что $J$
  индуцирует гомоморфизм $J_0:K_0 (bold(C)) -> K_0 (bold(C)_0)$. Из
  @prop:filtration-additivity-unipotence @cond:filtration-k0-additivity
  вытекает, что $j_0 compose J_0$ — тождественное отображение. Если
  $A in bold(C)_0$, то из рассмотрения тривиальной $bold(C)_0$-фильтрации
  следует, что $J_0 compose j_0[A]_(bold(C)_0)=[A]_(bold(C)_0)$.

  @cond:characteristic-devissage-k1-isomorphism Из наших предположений,
  очевидно, вытекает, что каждый объект $(A,alpha) in Sigma bold(C)$ обладает
  $Sigma bold(C)_0$-фильтрацией. Из части @cond:devissage-k0-isomorphism
  следует, что в диаграмме
  $ #devissage-composition-square() $
  существует отображение $I$, обратное к $i$ и определенное приведенным выше
  способом, с использованием $Sigma bold(C)_0$-фильтрации. Если мы покажем, что
  отображение $p_0 compose I$ мультипликативно, т. е. что
  $p_0 compose I[A,alpha beta]_(Sigma bold(C))
  =p_0 compose I([A,alpha]_(Sigma bold(C))+[A,beta]_(Sigma bold(C)))$
  для $alpha,beta in Aut_(bold(C)) (A)$, тогда будет существовать и
  индуцированное отображение $J_1:K_1 (bold(C)) -> K_1 (bold(C)_0)$, которое
  обратно к $j_1$.

  #source(318)Пусть $0=A_0 subset A_1 subset dots subset A_n=A$ —
  характеристическая $bold(C)_0$-фильтрация объекта $A$. Тогда она стабильна
  относительно действия автоморфизмов $alpha$ и $beta$. Пусть они индуцируют
  соответственно автоморфизмы $alpha_i$ и $beta_i$ на $B_i=A_i slash A_(i-1)$
  ($1 <= i <= n$). Применяя @prop:filtration-additivity-unipotence
  @cond:filtration-k0-additivity к группе $K_0 (Sigma bold(C))$ и аксиому
  @ax:abelian-k1-composition из определения группы $K_1 (bold(C)_0)$, получаем,
  что
  $
    p_0 (I[A,alpha beta])=p_0 (sum_i [B_i,alpha_i beta_i]_(Sigma bold(C)_0))
    =sum_i [B_i,alpha_i beta_i]_(bold(C)_0)
    =sum_i ([B_i,alpha_i]_(bold(C)_0)+[B_i,beta_i]_(bold(C)_0))
    =p_0 (I([A,alpha]_(Sigma bold(C))+[A,beta]_(Sigma bold(C)))).
  $
  Это завершает доказательство теоремы @th:devissage-k-isomorphisms.
]

#theorem[
  Пусть $bold(A)$ — абелева категория, в которой длина каждого из объектов
  конечна. Пусть $bold(A)_0$ — полная подкатегория полупростых объектов
  категории $bold(A)$. Тогда:
  #condition-list[
    #condition-item(format: "cyrillic")[вложение $bold(A)_0 subset bold(A)$
      индуцирует изоморфизмы $K_i (bold(A)_0) -> K_i (bold(A))$ ($i=0,1$);]
    <cond:finite-length-k-devissage>

    #condition-item(format: "cyrillic")[если ${S_j | j in J}$ — множество
      представителей классов изоморфных простых объектов категории $bold(A)_0$,
      то $K_0 (bold(A)_0)$ — свободная абелева группа с базисом
      ${[S_j] | j in J}$;]
    <cond:finite-length-k0-simple-basis>

    #condition-item(format: "cyrillic")[если $D_j=End_(bold(A)) (S_j)$, то $D_j$
      — тело, а группа $K_1 (bold(A)_0)$ является прямой суммой
      $ product.co_(j in J) (D_j^* slash [D_j^*,D_j^*]) $
      факторгрупп по коммутанту мультипликативных групп $D_j^*$ тел $D_j$.]
    <cond:finite-length-k1-division-units>
  ]
] <th:finite-length-k-groups>

*Замечание.* Если положить $K_i (R)=K_i (bold(P)(R))$ для кольца $R$ (это
обозначение будет введено в гл.~@ch:projective-k-theory), то утверждения
@cond:finite-length-k0-simple-basis и @cond:finite-length-k1-division-units
приведенной теоремы можно записать так:
$ K_i (bold(A)_0) tilde.eq product.co_(j in J) K_i (D_j) quad (i=0,1). $
(См. @ch:stable-projective-structure, §~@sec:semilocal-projective-modules или
@ch:stable-linear-groups, §~@sec:normal-subgroups-relative-k1.)

#proof[
  Если $A in bold(A)$, то через $s(A)$ обозначим наибольший полупростой
  подобъект объекта $A$. Условия обрыва цепей для подобъектов объекта $A$ и
  утверждение @prop:semisimple-complement о том, что конечная прямая сумма
  простых объектов является полупростым объектом, влекут за собой существование
  подобъекта $s(A)$, являющегося, конечно, вполне инвариантным подобъектом. При
  этом $s(A)!=0$, если $A!=0$ (следует обратить внимание лишь на основание ряда
  Жордана — Гёльдера). Проводя индукцию по $n$, определим теперь $A_n subset A$
  исходя из того, что $A_0=0$ и $A_(n+1) slash A_n=s(A slash A_n)$. Сделанные
  замечания показывают, что $A_n=A$ для некоторого $n$ (зависящего от $A$) и что
  $f(A_n) subset B_n$ для любого $f:A -> B$ из категории $bold(A)$. В частности,
  каждый объект категории $bold(A)$ обладает характеристической
  $bold(A)_0$-фильтрацией. Поэтому часть @cond:finite-length-k-devissage теоремы
  следует из теоремы @th:devissage-k-isomorphisms.

  #source(319)Так как категория $bold(A)_0$ полупростая и длина каждого объекта
  $A$ конечна, то из §~@sec:semisimplicity-wedderburn гл.~@ch:rings-modules
  следует, что $A tilde.eq product.co_j S_j^(n_j)$, где почти все $n_j=0$, и что
  $End_(bold(A)_0) (A)=product_j M_(n_j) (D_j)$. Следовательно,
  $Aut_(bold(A)_0) (A)=product_j GL_(n_j) (D_j)$. Если мы перейдем к
  факторгруппам этих групп по коммутанту, а затем к пределу, как в
  §~@sec:cofinal-functors гл.~@ch:exact-k-sequences, расширяя $A$, то получим,
  что
  $
    K_1 (bold(A)_0)=product.co_j (GL (D_j) slash [GL (D_j),GL (D_j)])
    =product.co_j K_1 (D_j).
  $
  В силу теоремы Дьёдонне @th:dieudonne-linear-abelianization естественное
  отображение $D_j^* slash [D_j^*,D_j^*] -> K_1 (D_j)$ является изоморфизмом.
  Если $d in D_j^*$, то образ $d$ соответствует элементу
  $[S_j,d] in K_1 (bold(A)_0)$, что и требовалось доказать.
]

#corollary[
  Пусть $A$ — коммутативное кольцо и $bold(A)$ — категория $A$-модулей конечной
  длины. Тогда
  $
    K_i (bold(A)) tilde.eq product.co_(frak(m) in maxSpec (A)) K_i (A slash
      frak(m)) quad (i=0,1).
  $
  Здесь $K_0 (A slash frak(m)) tilde.eq Int$ и
  $K_1 (A slash frak(m)) tilde.eq U (A slash frak(m))$ для каждого
  $frak(m) in maxSpec (A)$. Принятое соглашение в обозначениях:
  $K_i (B)=K_i (bold(P)(B))$ для кольца $B$.
] <cor:commutative-finite-length-k-groups>
