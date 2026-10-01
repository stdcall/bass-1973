#import "main-defs.typ": (
  Aut, End, Int, K, Ker, det, idx, ob, rad, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, named-axiom, proof, theorem,
)

== Теорема Робертса <sec:roberts-theorem>

В этом параграфе мы _зафиксируем алгебраически замкнутое поле $k$ и
$k$-категорию $bold(A)$_. Напомним (см. гл.~@ch:module-categories), что
$bold(A)$ — абелева категория, в которой $bold(A)(A,B)$ есть $k$-модуль для всех
$A,B in bold(A)$, при этом композиция отображений в категории $bold(A)$ является
$k$-билинейной. _Допустим далее, что все векторные пространства $bold(A)(A,B)$
конечномерны над $k$._

Примером такой категории является категория когерентных пучков модулей над
структурным пучком на полном алгебраическом многообразии над $k$. Именно для
этого примера Лесли Робертс #source(342)доказал в своей диссертации в
Гарвардском университете следующую теорему.

#theorem(title: [Робертс])[
  #idx("теорема Робертса")
  Пусть $k$ — алгебраически замкнутое поле, и пусть $bold(A)$ — $k$-категория, в
  которой $bold(A)(A,B)$ — конечномерное векторное пространство над $k$ для всех
  $A,B in bold(A)$. Тогда имеет место изоморфизм
  $ f:K_0 (bold(A)) tensor_Int k^* -> K_1 (bold(A)), $
  для которого $f([A]_(bold(A)),a)=[A,a dot 1_A]_(bold(A))$, если $A in bold(A)$
  и $a in k^*$.
] <th:roberts-k1-isomorphism>

#proof[
  Отображение $(A,a) mapsto [A,a dot 1_A]_(bold(A))$ из $ob bold(A) times k^*$ в
  $K_1 (bold(A))$, очевидно, аддитивно на точных последовательностях по первому
  аргументу (аксиома @ax:abelian-k0-additivity для $K_1 (bold(A))$) и аддитивно
  на произведениях по второму аргументу (аксиома @ax:abelian-k1-composition для
  $K_1 (bold(A))$). Следовательно, гомоморфизм $f$ определен корректно. Мы
  хотели бы построить обратное отображение для $f$.

  Пусть $(A,alpha) in Sigma bold(A)$. Подалгебра
  $k[alpha] subset End_(bold(A)) (A)$ конечномерна. Следовательно,
  $k[alpha] tilde.eq k[X] slash (P_alpha (X))$, где $P_alpha$ — приведенный
  многочлен наименьшей степени среди тех, для которых $P_alpha (alpha)=0$. Так
  как поле $k$ алгебраически замкнуто, то $P_alpha (X)=product_i (X-a_i)^(n_i)$,
  где все $a_i$ различны и лежат в $k^*$, поскольку отображение $alpha$
  обратимо. В силу китайской теоремы об остатках @prop:chinese-remainder-modules
  $k[alpha] tilde.eq product_i (k[X] slash ((X-a_i)^(n_i)))$. Пусть
  $1=sum_i e_i$ — разложение $1$ в сумму неразложимых идемпотентов
  $e_i in k[alpha]$, соответствующих приведенному произведению. Это разложение
  индуцирует разложение $A=product.co_i e_i A$. Можно дать более прозрачное
  описание для $e_i A$:
  $e_i A=Ker (alpha-a_i 1_A)^(n_i)=union.big_(n>0) Ker (alpha-a_i 1_A)^n$. Если
  $a in k$ и $a$ не совпадает ни с одним из $a_i$, то отображение
  $alpha-a dot 1_A$ обратимо. Таким образом, объединение
  $ A_alpha (a)=union.big_(n>0) Ker (alpha-a dot 1_A)^n $
  существует и равно нулю почти для всех $a$. Кроме того, имеет место разложение
  в прямую сумму в категории $Sigma bold(A)$:
  $ (A,alpha)=product.co_(a in k^*) (A_alpha (a),alpha_a), $
  <eq:roberts-generalized-eigenspace-decomposition>
  где автоморфизмы $alpha_a$ объекта $A_alpha (a)$ индуцированы автоморфизмом
  $alpha$. Так как $(alpha_a-a 1_(A_alpha (a)))^n=0$ для некоторого $n>0$, то
  автоморфизм $beta=a^(-1) alpha_a$ унипотентен. В силу
  @prop:filtration-additivity-unipotence @cond:unipotent-k1-vanishing
  $[A_alpha (a),beta]=0$ в группе $K_1 (bold(A))$. Поскольку $alpha_a=a beta$,
  то
  $[A_alpha (a),alpha_a]=[A_alpha (a),a 1_(A_alpha (a))]$
  в группе $K_1 (bold(A))$. Применяя равенство
  @eq:roberts-generalized-eigenspace-decomposition, получаем из этого, что для
  любого объекта $(A,alpha) in Sigma bold(A)$ имеет место #source(343)равенство
  $
    [A,alpha]=sum_(a in k^*) [A_alpha (a),a dot 1_(A_alpha (a))]
    =f(sum_(a in k^*) [A_alpha (a)] tensor a).
  $
  Это подсказывает нам, что надо строить обратное отображение к $f$, вводя в
  рассмотрение отображение
  $
    g:ob Sigma bold(A) -> K_0 (bold(A)) tensor k^*,
    quad g(A,alpha)=sum_(a in k^*) [A_alpha (a)] tensor a.
  $
  <eq:roberts-inverse-map>
  Предположим, что такое отображение $g$ действительно индуцирует гомоморфизм
  $g:K_1 (bold(A)) -> K_0 (bold(A)) tensor k^*$. Тогда из приведенной формулы
  следует, что $f compose g$ является тождественным отображением группы
  $K_1 (bold(A))$. Если идти в обратном направлении, то очевидно, что
  $g(f([A] tensor a))=g([A,a 1_A])=[A] tensor a$. Таким образом, теорема будет
  доказана, как только мы покажем, что отображение @eq:roberts-inverse-map
  индуцирует гомоморфизм группы $K_1 (bold(A))$. Нам надо проверить следующие
  условия: #named-axiom[если последовательность
    $0 -> (A,alpha) -> (B,beta) -> (C,gamma) -> 0$ точна в $Sigma bold(A)$, то
    $g(B,beta)=g(A,alpha)+g(C,gamma)$;] <ax:roberts-exact-additivity>

  #named-axiom[если $A in bold(A)$ и $alpha,beta in Aut_(bold(A)) (A)$, то
    $g(A,alpha beta)=g(A,alpha)+g(A,beta)$.] <ax:roberts-multiplicativity>

  _Проверка условия #[@ax:roberts-exact-additivity]._
  Пусть $h:(A,alpha) -> (B,beta)$ — морфизм из категории $Sigma bold(A)$. Итак,
  $h alpha=beta h$. Тогда если $a in k$, то
  $h(alpha-a dot 1_A)^n=(beta-a dot 1_B)^n h$ для всех $n>0$, поэтому
  $h(A_alpha (a)) subset B_beta (a)$. Из этого следует, что $h$ является прямой
  суммой морфизмов $h_a:(A_alpha (a),alpha_a) -> (B_beta (a),beta_a)$
  ($a in k^*$). В частности, точная последовательность из условия
  @ax:roberts-exact-additivity расщепляется на этом пути в прямую сумму точных
  последовательностей
  $
    0 -> (A_alpha (a),alpha_a) -> (B_beta (a),beta_a)
    -> (C_gamma (a),gamma_a) -> 0
  $
  ($a in k^*$). Таким образом, $[B_beta (a)]=[A_alpha (a)]+[C_gamma (a)]$ в
  группе $K_0 (bold(A))$ (аксиома @ax:abelian-k0-additivity для группы
  $K_0 (bold(A))$), поэтому справедливость условия @ax:roberts-exact-additivity
  немедленно вытекает из определения @eq:roberts-inverse-map отображения $g$.

  _Проверка условия #[@ax:roberts-multiplicativity]._ Проведем ее в несколько
  шагов.
  #condition-list[
    #condition-item[(см. @ch:rings-modules, §~@sec:semisimplicity-wedderburn–
      @sec:jacobson-radical-idempotents). Пусть $E$ — конечномерная $k$-алгебра.
      Тогда $rad E$ — нильпотентный идеал, а $overline(E)=E slash rad E$ —
      конечное произведение колец матриц над алгебрами с делением. Поскольку
      поле $k$ алгебраически замкнуто, все алгебры с делением тривиальны, и
      поэтому $overline(E)$ — конечное произведение алгебр вида $M_n (k)$. Любое
      (конечное) множество ортогональных идемпотентов из $overline(E)$ можно
      поднять до ортогонального множества идемпотентов в $E$ (см.
      @prop:orthogonal-idempotent-lifting). В частности, если $e$ — ненулевой
      идемпотент в $E$, #source(344)то он неразложим тогда и только тогда, когда
      его образ $overline(e) in overline(E)$ неразложим ($e$ называется
      неразложимым, если $e!=0$ и $e$ не является суммой двух ненулевых
      ортогональных идемпотентов). Учитывая строение алгебры $overline(E)$,
      получаем, в частности, что алгебра $E$ не содержит нетривиальных
      идемпотентов (т. е. $1$ — неразложимый идемпотент) тогда и только тогда,
      когда $overline(E)=k$, но это означает, что $E$ является (не обязательно
      коммутативным) локальным кольцом.]
    <cond:roberts-finite-algebra>

    #condition-item[Пусть $B$ — ненулевой неразложимый объект категории
      $bold(A)$ и $A=B^n$ для некоторого $n>0$. Если $R=End_(bold(A)) (B)$, то
      $E=End_(bold(A)) (A) tilde.eq M_n (R)$. Сделанные выше замечания
      показывают, что $R$ — локальное кольцо с полем вычетов $overline(R)=k$.
      Поэтому $overline(E) tilde.eq M_n (k)$. Этот изоморфизм определяется
      объектом $A$ с точностью до внутреннего автоморфизма. Таким образом,
      определитель
      $ det:overline(E) -> k $
      определен корректно.

      Пусть $C$ — неразложимый объект, который не изоморфен $B$. Пусть
      $B arrow.r^h C arrow.r^(h') B$ — морфизмы категории $bold(A)$. Если бы
      $h' h ∉ rad R$, то мы получили бы автоморфизм объекта $B$, а из этого
      следовало бы, что $B$ является прямым слагаемым объекта $C$, что
      противоречит его неразложимости. Итак, $h' h in rad R$. Отсюда следует
      более общее утверждение: если $B^n arrow.r^h C^m arrow.r^(h') B^n$ —
      морфизмы категории $bold(A)$, то $h' h in rad End_(bold(A)) (B^n)$
      (поскольку $rad M_n (R)=M_n (rad R)$, что уже использовалось и ранее; см.
      @prop:radical-morita-invariance).]
    <cond:roberts-isotypic-blocks>

    #condition-item[Пусть $A$ — любой объект категории $bold(A)$. В силу теоремы
      Крулля — Шмидта для $bold(A)$ (см. @th:krull-schmidt) можно разложить
      $A=product.co_j A_j$, причем $A_j tilde.eq B_j^(n_j)$ и $B_j$ — попарно
      неизоморфные неразложимые объекты. Кроме того, любое другое разложение $A$
      в прямую сумму неразложимых подобъектов получается из этого разложения с
      помощью автоморфизма объекта $A$.

      Пусть $E=End_(bold(A)) (A)$ и
      $E_j=End_(bold(A)) (A_j) tilde.eq M_(n_j) (R_j)$, где
      $R_j=End_(bold(A)) (B_j)$. Указанное разложение объекта индуцирует
      мономорфизм $k$-алгебр:
      $ h:product_j E_j -> E, $
      который зависит от выбора разложения с точностью до внутреннего
      автоморфизма объекта $E$. Мы хотим показать, что $h$ индуцирует изоморфизм
      $ overline(h):product_j overline(E)_j arrow.r^tilde overline(E). $
      Это равносильно тому, что $rad E$ является суммой всех
      $rad bold(A)(A_i,A_i)$ и всех $bold(A)(A_i,A_j)$ ($i!=j$). Из второго
      абзаца части @cond:roberts-isotypic-blocks следует, что эта сумма
      действительно является идеалом, который мы обозначим через $I$. Очевидно,
      что $h$ индуцирует изоморфизм из $product_j overline(E)_j$ #source(345)в
      $E slash I$. Осталось показать, что $I subset rad E$. Для этой цели
      достаточно заметить, что если $alpha in E$ и $alpha equiv 1 mod I$, то
      отображение $alpha$ обратимо. Запишем $alpha$ в матричной форме:
      $alpha=(alpha_(i j))$, $alpha_(i j) in bold(A)(A_i,A_j)$. Так как
      $alpha_(j j) equiv 1 mod rad E_j$, то все $alpha_(j j)$ обратимы. С
      помощью элементарных преобразований столбцов можно преобразовать первую
      строку к виду $(alpha_(1 1),0,dots,0)$. Это изменяет $alpha_(j j)$ ($j>1$)
      на суммы морфизмов $A_j -> A_j$, проходящих через некоторое $A_k$, $k!=j$.
      Таким образом, в силу @cond:roberts-isotypic-blocks все $alpha_(j j)$ не
      меняются по модулю $rad E_j$. Теперь можно перейти к матрице меньшего
      размера, отбрасывая первую строку и первый столбец, и продолжить этот
      процесс. В конце концов с помощью элементарных операций мы приведем
      матрицу к треугольному виду:
      $
        alpha'=mat(alpha'_(1 1), , 0; , dots.down, ; *, , alpha'_(n n))
        =mat(1, , 0; , dots.down, ; *, , 1)
        mat(alpha'_(1 1), , 0; , dots.down, ; 0, , alpha'_(n n)).
      $
      Так как все $alpha'_(j j)$ обратимы, то обратима и матрица $alpha'$.
      Поскольку элементарные операции являются умножениями на обратимые матрицы,
      первоначальная матрица $alpha$ также обратима.

      Пусть теперь $alpha in Aut_(bold(A)) (A)$. Тогда образ
      $overline(alpha) in overline(E)$ можно записать таким образом:
      $overline(alpha)=(overline(alpha)_j)$
      ($overline(alpha)_j in overline(E)_j$). Напомним, что
      $overline(E)_j tilde.eq M_(n_j) (k)$, поэтому
      $det (overline(alpha)_j) in k^*$. Положим
      $
        g'(A,alpha)=sum_j [B_j] tensor det (overline(alpha)_j)
        in K_0 (bold(A)) tensor k^*.
      $
      Априори это определение зависит от выбранного разложения объекта $A$.
      Однако любые два разложения отличаются друг от друга на внутренний
      автоморфизм алгебры $E$. Это не затрагивает классы изоморфных объектов в
      $B_j$, а меняет лишь $overline(alpha)_j$ на сопряженные. Следовательно,
      $[B_j] tensor det (overline(alpha)_j)$ не меняется для каждого $j$ при
      новом выборе, поэтому отображение $g'$ определено корректно. Если также
      $beta in Aut_(bold(A)) (A)$, то
      $
        g'(A,alpha beta)=sum_j [B_j] tensor det (overline(alpha beta)_j)
        =sum_j [B_j] tensor det (overline(alpha)_j overline(beta)_j)
        =sum_j (([B_j] tensor det overline(alpha)_j)
          +([B_j] tensor det overline(beta)_j))=g'(A,alpha)+g'(A,beta).
      $
    ] <cond:roberts-endomorphism-radical>

    #condition-item[Ввиду последнего замечания можно закончить проверку условия
      @ax:roberts-multiplicativity для $g$, а следовательно, и доказательство
      теоремы, если показать, что
      $ g(A,alpha)=g'(A,alpha) quad "для" quad (A,alpha) in Sigma bold(A). $
      Предположим сначала, что также $(B,beta) in Sigma bold(A)$. Можно
      разложить $C=A plus.o B$ в прямую сумму неразложимых объектов, #source(
        346,
      )разлагая сначала $A$ и $B$ отдельно, а затем объединяя эти разложения. В
      результате получаем разложение $C=product.co_j C_j$, как в части
      @cond:roberts-endomorphism-radical, где
      $C_j tilde.eq D_j^(n_j) plus.o D_j^(m_j)$, $D_j$ — неразложимый объект,
      первое слагаемое лежит в $A$, а второе в $B$. Подсчитывая
      $g'(A plus.o B,alpha plus.o beta)$ из этого разложения, видим, что
      $overline(alpha plus.o beta)_j
      =mat(overline(alpha)_j, 0; 0, overline(beta)_j)$ в матричном виде в
      $End_(bold(A)) (C_j) slash rad End_(bold(A)) (C_j)$, поэтому
      $det (overline(alpha plus.o beta)_j)
      =det (overline(alpha)_j) det (overline(beta)_j)$. Следовательно,
      $
        g'(A plus.o B,alpha plus.o beta)
        =sum_j [D_j] tensor det (overline(alpha plus.o beta)_j)
        =sum_j [D_j] tensor det (overline(alpha)_j)
        +sum_j [D_j] tensor det (overline(beta)_j)=g'(A,alpha)+g'(B,beta).
      $

      Чтобы доказать равенство $g=g'$, запишем, как и в
      #[@eq:roberts-generalized-eigenspace-decomposition]:
      $(A,alpha)=product.co_(a in k^*) (A_alpha (a),alpha_a)$. Из последнего
      абзаца следует, что достаточно доказать равенство
      $g(A_alpha (a),alpha_a)=g'(A_alpha (a),alpha_a)$ для каждого $a$. Другими
      словами, можно все свести к случаю, когда $(alpha-a 1_A)^n=0$ для
      некоторого $a in k$, а следовательно, $g(A,alpha)=[A] tensor a$.

      Пусть $A=product.co_j A_j$, $A_j tilde.eq B_j^(n_j)$, как в
      @cond:roberts-endomorphism-radical. Так как теперь $(alpha-a dot 1)^n=0$ в
      $E$ ($n>0$), то $(overline(alpha)-a dot 1)^n=0$ в $overline(E)$ и,
      следовательно, аналогично для каждого $overline(alpha)_j$. Отсюда
      вытекает, что $a$ — единственное собственное значение матрицы
      $overline(alpha)_j in M_(n_j) (k)$. Поэтому
      $det (overline(alpha)_j)=a^(n_j)$. Таким образом,
      $
        g'(A,alpha)=sum_j [B_j] tensor a^(n_j)=sum_j n_j [B_j] tensor a
        =[product.co_j B_j^(n_j)] tensor a=[A] tensor a=g(A,alpha),
      $
      что и требовалось доказать.]
    <cond:roberts-inverse-coincidence>
  ]
]
