#import "@preview/theorion:0.3.3": *
#import "@preview/cetz:0.3.4"
#import "@preview/cetz-plot:0.1.1"
#import math: *

#import cosmos.rainbow: *

#let func(caption, size, domain, f, ..options) = {
  figure(
    cetz.canvas({
      import cetz.draw: *
      import cetz-plot: plot
      plot.plot(
        size: size,
        axis-style: "school-book",
        x-tick-step: none,
        y-tick-step: none,
        ..options,
        {
          for fun in f {
            plot.add(domain: domain, samples: 1000, fun)
          }
        },
      )
    }),
    numbering: none,
    gap: 1em,
    caption: caption,
  )
}
#let inverseFunc(caption, size, domain, f, ..options) = {
  figure(
    cetz.canvas({
      import cetz.draw: *
      import cetz-plot: plot
      plot.plot(
        size: size,
        axis-style: "school-book",
        x-tick-step: none,
        y-tick-step: none,
        ..options,
        {
          for fun in f {
            plot.add(domain: domain, samples: 100, axes: ("y", "x"), fun)
          }
        },
      )
    }),
    numbering: none,
    caption: caption,
  )
}

#show: show-theorion

#set text(lang: "it")
#set page(numbering: "I", footer: [], header: context {
  if counter(page).display() != "I" {
    if calc.even(counter(page).get().at(0)) {
      align(left, [#{ counter(page).display() } - _Analisi Matematica I_])
    } else {
      align(right, [_Analisi Matematica I_ - #{ counter(page).display() }])
    }
  }
})

#align(center, heading(outlined: false, [Analisi Matematica I]))
#align(
  center,
  [Andrea Giurgola - Prof. Fabio Punzo \ Ingegneria Elettronica, Politecnico di Milano],
) \

#set heading(numbering: "1.1.")
#set-theorion-numbering("1.1")
#outline(title: [Indice])

#pagebreak()
#counter(page).update(1)
#set page(numbering: "1")
= Richiamo di logica

La logica si basa su *predicati* (o *affermazioni*), i quali possono essere veri o falsi e si connettono tra loro tramite connettivi:
- *Implicazione logica* ($=>$): se l'antecedente è vero allora anche il conseguente sarà vero, ma non vale il contrario
- *Equivalenza logica* ($<=>$): la verità di uno dei due predicati implica la verità dell'altro e viceversa
- *Contrapposizione*: data un'implicazione ($p => q$) allora sarà anche vero l'implicazione di senso inverso degli opposti dei due predicati (se $p => q$, allora anche $overline(q) => overline(p)$)

Alla base della matematica esiste il *teorema*, ossia un'implicazione logica in cui l'antecedente si dice *ipotesi* e il conseguente si dice *tesi*. La *dimostrazione* è una catena di passaggi logici che giustifica tale implicazione. Esistono tre tipi di dimostrazioni:
- *Diretta*: viene dimostrato che l'ipotesi implica la tesi
- *Indiretta per contrapposizione*: viene dimostrato che l'inverso della tesi implica l'inverso dell'ipotesi
- *Indiretta per assurdo*: viene dimostrato che la negazione della tesi porta ad un risultato falso, rendendo dunque vera la tesi
- *Per induzione*: un tipo di dimostrazione che vale solo all'interno dei numeri naturali

Esistono tre quattro diverse tipologie di teorema:
- *Lemma*: un teorema di piccola importanza
- *Proposizione*: un teorema di media importanza
- *Teorema*
- *Corollario*: l'insieme di conseguenze di un teorema

== Il principio di induzione

Il *principio di induzione* è un principio dimostrativo che permette di dimostrare un teorema in $NN$ riducendo notevolmente il numero di passaggi necessari. \
Sia $p(n)$ una proposizione logica che dipende dalla variabile $n in NN$. Se $p(n)$ è valida per $n = 0$ (*ipotesi* o *base induttiva*), allora sarà vera anche per $n = 0 + 1$ (*passo induttivo*), e così via. Secondo il principio di induzione, allora $p(n)$ è vera $forall n in NN$. Di seguito tre esempi di teoremi dimostrabili con il principio di induzione.

#theorem(
  title: [Somma dei primi $n$-naturali],

  [$ sum^n_(k=1)k = n/2(n+1), forall n in NN $
  ],
)
#proof([
  Sia $p(n)$ la suddetta relazione. \
  $p(0)$: $0 = 0/2(0+1), 0 = 0$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $1 + 2 + 3 + ... + n + (n + 1) = (n + 1)/2[(n + 1) + 1]$ \
  Riscrivendo la somma fino a $n$ come $p(n)$ \
  $(1 + 2 + 3 + ... + n) + (n + 1) = n/2(n + 1) + (n + 1) = (n + 1)(n/2 + 1) = (n + 1)((n + 2)/2) = (n + 1)/2(n + 1 + 1)$. \ In quanto si è ritornati alla scrittura di $p(n + 1)$, allora è verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, il teorema vale $forall n in NN$.
]) \ \

#theorem(title: [Disuguaglianza di Bernoulli], [
  Sia $h in RR, h > -1$. Pertanto $(1+h)^n >= 1 + n h, forall n in NN$.
]) <ind:brn>
#proof([
  Sia $p(n)$ la suddetta disuguaglianza. \
  $p(0)$: $(1 + h)^0 >= 1 + 0, 1 >= 1$. Pertanto $p(0)$ è verificata.\
  $p(n + 1)$: $(1 + h)^(n + 1) >= 1 + (n + 1)h$ \
  $(1 + h)^(n + 1) = (1 + h)^n (1 + h)$. Si nota che $1 + h > 0$ e che $(1 + h)^n >= (1 + n h)$. Dunque \
  $(1 + h)^n (1 + h) >= (1 + n h)(1 + h) = n h^2 + n h + h + 1$. Dunque \
  $(1 + h)^(n + 1) >= n h^2 + n h + h + 1$. $n h^2$ si può non considerare in quanto rende solo più forte la relazione di disuguaglianza. Dunque \
  $(1 + h)^(n + 1) >= n h + h + 1, (1 + h)^(n + 1) >= 1 + (n + 1)h$. \
  È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

#proposition(
  title: [Somma della progressione geometrica],
  [
    Sia $q in RR, q != 1$. $sum^n_(k = 0)q^k = (1 - q^(n + 1))/(1 - q), forall n in NN$
  ],
)
#proof([#set par(leading: 1.065em); Sia $p(n)$ la suddetta proposizione. \
  $p(0)$: $q^0 = (1 - q^1)/(1 - q), 1 = cancel(1 - q)/cancel(1 - q), 1 = 1$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $sum^(n + 1)_(k = 0)q^k = (1 - q^(n + 2))/(1 - q), sum^(n + 1)_(k = 0)q^k = sum^(n)_(k = 0)q^k + q^(n + 1) = (1 - q^(n + 1))/(1 - q) + q^(n + 1) =$ \
  $= (1 - cancel(q^(n + 1)) + cancel(q^(n + 1)) - q^(n + 2))/(1 - q) = (1 - q^(n + 2))/(1 - q)$. \ È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

= I numeri

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ NN := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ ZZ := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ QQ := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$. \ \

== I numeri razionali

Due frazioni $a/b$ e $c/d$ si dicono *equivalenti* se vale la relazione $a d = b c$. \

I numeri razionali possono anche essere rappresentati sotto forma di *allineamento decimale* (per esempio $1/2 = 0,5$). Un numero razionale può essere:
- *finito*: la parte decimale ha un numero limitato di cifre
- *periodico*: la parte decimale si ripete all'infinito con costanza

#note-box([Gli allineamenti decimali con periodo $9$ non provengono da alcuna divisione (ad esempio $0.overline(9) = 1$).])

#definition(title: [Numeri pari e dispari], [
  Sia $n in ZZ$. $n$ si dice:
  - _pari_: $exists h in ZZ : n = 2h$
  - _dispari_: $exists h in ZZ : n = 2h + 1$
]) <raz:defpari>
#proposition(
  title: [Parità dei quadrati],
  [$n$ pari $=> n^2$ pari, $n$ dispari $=> n^2$ dispari],
) <raz:pdq>
#proof([\ Sia $n in ZZ$. $n$ è pari $<=> exists h in ZZ : n = 2h$. Dunque \
  $n^2 = (2h)^2 = 4h^2 = 2(2h^2) = 2k$, essendo $k = 2h^2 in ZZ$. \
  Dunque $n^2$ è pari \ \
  Sia $n in ZZ$. $n$ è dispari $<=> exists h in ZZ : n = 2h + 1$. Dunque \
  $n^2 = (2h +1)^2 = 4h^2 + 4h + 1 = 2(2h^2 +2h) + 1 = 2k + 1$ dove $k = 2h^2 + 2h$. \
  Dunque $n^2$ è dispari
])
#proposition(
  title: [Parità dei quadrati inversa],
  [$n^2$ pari $=> n$ pari, $n^2$ dispari $=> n$ dispari],
) <raz:pdq2>
#proof([Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ])

=== Il problema delle radici

I numeri razionali presentano lacune in materia di estrazione di radici.
#definition(
  title: [Radice quadrata],
  [Sia $a >= 0$. Si dice _radice quadrata_ di $a$ un numero $b$ tale che $b^2 = a, b >= 0$.],
)
#theorem(
  title: [Irrazionalità di $sqrt(2)$],
  [$sqrt(2)$ non è un numero razionale.],
)
#proof([
  Supponiamo, per assurdo, che $sqrt(2) in QQ$. Dunque
  $sqrt(2) = m/n$ con $m,n in ZZ, n != 0, m, n$ primi tra loro. Elevando al quadrato: \
  $2 = m^2/n^2 => m^2 = 2n^2$. Pertanto, per la @raz:pdq, $m^2$ è pari e anche $m$ è pari. \ Dunque $exists k in Z : m = 2k$ \
  $2n^2 = m^2 = (2k)^2 = 4k^2 => 2n^2 = 4k^2 => n^2 = 2k^2$. Pertanto, per la @raz:pdq, $n^2$ è pari, quindi anche $n$ è pari.
  Questo è un assurdo, dal momento che $m$ e $n$ sono per definizione primi tra loro, quindi non possono essere entrambi pari.
]) \ \

== I numeri reali

L'insieme dei numeri reali rappresenta quell'insieme numerico che comprende *tutti gli allineamenti decimali finiti*,* infiniti periodici* e *infiniti non periodici*. Dunque:
$ NN subset ZZ subset QQ subset RR $

Tutti quei numeri reali che non sono razionali si dicono *numeri irrazionali*, i quali appartengono all'insieme $RR backslash QQ$.

Se si rappresentano i numeri razionali sulla retta, ci saranno sempre dei buchi (per es. ($sqrt(2) in RR$ ma $in.not QQ$). Invece i numeri reali, in quanto comprendono anche i non razionali, godono della *proprietà di continuità* (o *completezza*) *dei numeri reali*.
\
== Estremo superiore ed inferiore
Sia $E subset.eq RR$.
#definition(
  title: [Massimo e minimo di un insieme],
  [
    #set par(leading: 1.06em)
    - $M in RR$ si dice _massimo_ ($max E$) di E se $cases(M in E, M >= x\, forall x in E)$ \
    - $m in RR$ si dice _minimo_ ($min E$) di E se $cases(m in E, m <= x\,forall x in E)$
  ],
)
#example([$E = (0; 2] => max E = 2, exists.not min E$, $E = [0; 2) => exists.not max E, min E = 0$])
#definition(title: [Maggiorante e minorante di un insieme], [
  - $Lambda in RR$ si dice _maggiorante_ di E se $Lambda >= x, forall x in E$ \
  - $lambda in RR$ si dice _minorante_ di E se $lambda <= x, forall x in E$
])
#definition(title: [Estremi di un insieme], [Sia $E != emptyset$.
  - Si dice _estremo superiore_ ($sup E$) di E il minimo dei maggioranti
  - Si dice _estremo inferiore_ ($inf E$) di E il massimo dei minoranti.
])
#example($E = (0; 2] => sup E = 2 = max E, inf E = 0$)
#note-box([Se $exists max E$ allora coincide con $sup E$.])

L'estremo superiore è caratterizzato da due proprietà:
- $sup E$ è un maggiorante di E: $sup E >= x, forall x in E$
- Qualunque numero $< sup E$ non è un maggiorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon > sup E - epsilon$
L'estremo inferiore di E è caratterizzato da:
- $inf E$ è minorante di E: $inf E <= x, forall x in E$
- Qualunque numero $> inf E$ non è minorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon < inf E + epsilon$
\
#definition(
  title: [Limitatezza di un insieme],
  [
    + $E$ si dice _limitato superiormente_ se ammette almeno un maggiorante ($exists Lambda in RR, Lambda >= x, forall x in E$)
    + $E$ si dice _limitato inferiormente_ se ammette almeno un minorante ($exists lambda in RR, lambda <= x, forall x in E$)
    + $E$ si dice _limitato_ se lo è sia inferiormente che superiormente ($exists Lambda, lambda in RR : lambda <= x <= Lambda, forall x in E$)
  ],
)
#note-box([
  + $E$ non è limitato superiormente $<=> exists x in E : x >= Lambda, forall Lambda in RR => sup E = +infinity$
  + $E$ non è limitato inferiormente $<=> exists x in E : x <= lambda, forall lambda in RR => inf E = -infinity$
])
#theorem(
  title: [Proprietà di continuità/completezza di $RR$],
  [
    Un insieme $E subset.eq RR != emptyset$ limitato superiormente ha sempre un $sup E$ in $RR$. Analogamente, un insieme $E$ limitato inferiormente ha sempre un $inf E$ in $RR$.
  ],
) <esi:pcrr>
#corollary([
  Se $E subset.eq RR != emptyset$, allora $exists sup E, inf E in RR$
])
#example([
  Sia $A = { x in QQ : x^2 <= 2 } subset.eq QQ subset.eq RR => sup A = sqrt(2)$ \
  In questo caso l'estremo superiore appartiene a $RR$ ma non a $QQ$, dunque osserviamo che in $QQ$ la proprietà di completezza è falsa. \
])

== Potenze e radici

Grazie alla proprietà di continuità di $RR$ vale il seguente teorema.
#theorem(
  title: [Radice $n$-esima di un numero],
  [
    Sia $n in NN, y in RR : n >= 1, y > 0$. Allora $exists x in RR : x^n = y$, dove $x$ si dice la _radice $n$-esima_ di $y$.
  ],
)

Siano $r = m/n, a > 0$, con $m in ZZ, n in NN, n != 0$. Allora si può dire che
$ a^r := (a^m)^(1/n) = root(n, a^m) $
Inoltre, se $n$ è dispari, vale anche la seguente relazione.
$ (-a)^r = -root(n, a^m) $
Ora siano $a > 0, b in RR$. $a^b$ rappresenta una *potenza ad esponente reale*. Dunque
$
  a > 1 <=> a^b := sup {a^r : r in QQ, r <= b} \
  a < 1 <=> a^b := sup {a^r : r in QQ, r >= b}
$
In altre parole, se consideriamo la potenza $a^b$ per un qualsiasi numero reale $b$, essa rappresenta l'estremo superiore dell'insieme delle potenze di $a$. Nel caso $a > 1$, gli esponenti delle potenze nell'insieme sono tutti minori o uguali di $b$, mentre nel caso $a < 1$, essi sono tutti maggiori di $b$.

#theorem(
  title: [Logaritmo di un numero in base $a$],
  [
    Siano $a > 0, a != 1, y > 0$. Allora $exists x in RR : a^x = y$ dove $x$ è detto il _logaritmo di $y$ in base $a$_.
  ],
)

== Valore assoluto

#definition(title: [Valore assoluto], [
  Si dice _valore assoluto_ o _modulo_ di un numero $x in RR$ \
  $ abs(x) := cases(x"   se" x >= 0, -x" se" x < 0) $
])
#warning-box([Sia $a in RR$. Allora $sqrt(a^2) = abs(a)$ poiché il risultato di una radice di ordine pari è sempre positivo.])

In altre parole, $abs(a) = max{a, -a} <=> abs(a) = abs(-a), a <= abs(a), -a <= abs(a)$.

#theorem(title: [Disuguaglianza triangolare], [
  $ abs(a + b) <= abs(a) + abs(b), forall a, b in RR $
]) <abs:dtr>
#proof([Siano $a, b in RR$. \
  Sapendo che $a <= abs(a)$ e $b <= abs(b)$ e che $-a <= abs(a)$ e $-b <= abs(b)$ e sommando membro a membro si ha \
  $a + b <= abs(a) + abs(b), -a -b <= abs(a) + abs(b)$ \
  In virtù del fatto che $abs(a) = max{a, -a}$ allora $abs(a + b) = max{a + b, -a - b} <= abs(a) + abs(b)$.
])

Analogamente, è vera anche la relazione $abs(abs(a) - abs(b)) <= abs(a + b), forall a, b in RR$.

== I numeri complessi

#show math.Im: "Im"
#show math.Re: "Re"

Se consideriamo l'equazione $x^2 + 1 = 0$, sappiamo che non esistono soluzioni in $RR$. Per poterla risolvere dobbiamo introdurre l'*unità immaginaria* $i$, per la quale vale la seguente proprietà.
#definition(title: "Unità immaginaria", $ i^2 = -1 $)
Risulta dunque che la suddetta equazione ha come soluzione $x = plus.minus i$. \
Con questa unità è possibile costruire i cosiddetti *numeri complessi*, i quali assumono la forma di $z = a + b i, z in CC, a, b in RR$. $a$ corrisponde alla *parte reale* di $z$ ($a = Re z$) mentre $b$ alla *parte immaginaria* ($b = Im z$). \

I numeri complessi possono assumere tre forme diverse:
- *Forma algebrica*: $z = a + b i, forall a,b in RR$
- *Forma trigonometrica*: $z = r(cos theta + i sin theta), forall r in RR, forall theta in [0 + 2k pi, 2pi + 2k pi), forall k in NN$
- *Forma esponenziale*: $z = r e^(i theta), forall r in RR, forall theta in (0 + 2k pi, 2pi + 2k pi), forall k in NN$

=== Operazioni tra numeri complessi

La somma tra $z = a + b i, w = c + d i in CC$ si svolge utilizzando le normali regole dell'algebra.
$ z + w = a + b i + c + d i = a + c + (b + d)i $
Analogamente, anche il prodotto si svolge allo stesso modo
$
  z w = (a + b i)(c + d i) = a c + b c i + a d i + b d i^2 = a c - b d + (b c + a d)i
$ \
L'*opposto* di un numero complesso è $-z = - a - b i$ mentre l'*inverso* non è così immediato. Infatti
$
  z^(-1) = (a + b i)^(-1) = 1/(a + b i) = 1/(a + b i)(a - b i)/(a - b i) = (a - b i)/(a^2 + b^2) = a/(a^2 + b^2) - b/(a^2 + b^2)i
$
Il quarto passaggio è necessario affinché si possa arrivare ad un forma che possa comunque ricondurre ad una parte reale ed una parte immaginaria distinte. \
Il *coniugato* di un numero complesso è lui stesso con la parte immaginaria invertita. Dunque
$ overline(z) = a - b i $
Il *modulo* di un numero complesso vale invece
$ abs(z) = sqrt(a^2 + b^2) $

Queste due formule ci permettono di riscrivere l'inverso e il prodotto tra $z$ e $overline(z)$ come
$ overline(z)z = abs(z)^2, z^(-1) = overline(z)/abs(z)^2 $
Risulta inoltre che il coniugato del prodotto $z w$ è uguale al prodotto dei coniugati ($overline(z w) = overline(z) dot overline(w)$)
Sappiamo anche che il modulo di $z$ ha le seguenti proprietà.
$
  abs(z) >= 0, forall z in CC, abs(z) = 0 <=> z = 0 \
  abs(Re z) <= abs(z), abs(Im z) <= abs(z)
$
E il coniugato ha queste altre proprietà.
$ z + overline(z) = 2 Re z, z - overline(z) = 2 Im z $
Infine la divisione tra due numeri complessi $z, w in CC, w != 0$ avviene come il prodotto, dunque
$ z/w = z 1/w = z overline(w)/abs(w)^2 $
#example([
  $(1 - 2i)/(1 + i) = (1 - 2i) 1/(1 + i) = (1 - 2i) (1 - i)/(1 + 1) = (1 - 2i) (1 - i)/2 = 1/2 (1 - 2i - i - 2) = 1/2 (1 - 3i)$
])
#theorem(title: [Disuguaglianza triangolare in $CC$], [
  $ abs(z + w) <= abs(z) + abs(w), forall z, w in CC $
])
\
=== Piano di Argand-Gauss

#grid(
  columns: 2,
  [Dato $z in CC, z = a + b i$ esso si può rappresentare nel cosiddetto *piano di Argand-Gauss* o, più comunemente, *piano di Gauss*. Basta far corrispondere all'ascissa la $Re z$ e all'ordinata la $Im z$.],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3, 3),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -1,
      y-max: 2,
      x-min: -1,
      x-max: 2,
      {
        plot.add(((0, 0), (calc.sqrt(3), 1)))
        plot.add(((0, 0), (calc.sqrt(3), -1)))
        plot.annotate({
          mark(
            (calc.sqrt(3), 1),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
          )
          mark(
            (calc.sqrt(3), -1),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
          )
          content((calc.sqrt(3) + 0.3, 1.35), $z = (a, b)$)
          content((calc.sqrt(3) + 0.3, -1.35), $overline(z) = (a, -b)$)
        })
      },
    )
  }),
)

=== Forma trigonometrica di $z$

Dato $z = x + y i$, diciamo $theta$ l'angolo che si forma tra il segmento $z$ è l'asse $x$. Questo ci permette di individuare $z$ utilizzando solo $abs(z)$, ossia la distanza da $z$ all'origine, e $theta$, detto anche *argomento* di $z$. Per tornare alla forma algebrica, è necessario calcolare $x$ e $y$, i quali valgono:
$
  x = abs(z)cos theta, y = abs(z)sin theta => z = abs(z)cos theta + i abs(z)sin theta = abs(z)(cos theta + i sin theta)
$
Ogni coppia $(abs(z), theta)$ individua uno e uno solo $z$.

Per convertire dalla forma algebrica alla forma trigonometrica, è necessario calcolare $abs(z)$ e $theta$. Notare che $theta$ è determinato a meno di multipli di $2 pi$, dunque è più appropriato considerare quel $theta in [0; 2pi)$ oppure in un qualsiasi intervallo semiaperto $[a, b)$ dove $b - a =2pi$. Perciò si parla di *argomento principale*. Per trovare $theta$ sappiamo che
$
  y/x = (cancel(abs(z))sin theta)/(cancel(abs(z)) cos theta) = (sin theta)/(cos theta) = tan theta \
  "se" x > 0 => theta = arctan(y/x), "se" x < 0 => theta = arctan(y/x) + pi
$

Il prodotto con la forma trigonometrica segue le normali regole dell'algebra e della goniometria. Siano $z = r(cos theta + i sin theta), w = R(cos phi + i sin phi)$. Allora
$
  z w &= r R(cos theta + i sin theta)(cos phi + i sin phi) = \
  &= r R(cos theta cos phi + i sin theta cos phi i cos theta sin phi + i^2 sin theta sin phi) = \
  &= r R(underbracket(cos theta cos phi - sin theta sin phi, cos (theta + phi)) + i(underbracket(cos theta sin phi + sin theta cos phi, sin (theta + phi)))) = \
  &= r R(cos (theta + phi) + i sin (theta + phi))
$

Dunque il prodotto tra due numeri complessi $z$ e $w$ presenta come modulo il prodotto dei moduli e come argomento la somma degli argomenti.
#note-box([In altre parole, moltiplicare $z$ per $w$ agisce come:
  - _dilatazione_ o _compressione_ di $abs(z)$ (in base a se $abs(w) > 1$ o $abs(w) < 1$)
  - _rotazione_ di $z$ di angolo $phi$
])
Grazie a questa caratteristica, è possibile ottenere una formula analoga per le potenze.
#definition(
  title: [Formula di De Moivre],
  [
    Sia $z = r(cos theta + i sin theta), n in NN$. Allora $z^n = r^n (cos n theta + i sin n theta)$
  ],
)
Questa formula rende comoda l'elevazione a potenza di numeri complessi, che in forma algebrica sarebbe invece molto tediosa. \ \ \ \ \

=== Forma esponenziale di $z$

La forma esponenziale di un numero complesso si fonda sull'*identità di Eulero*.
#definition(
  title: [Identità di Eulero],
  $ e^(i theta) = cos theta + i sin theta $,
)
Dunque, prendendo l'esempio precedente del prodotto tra $z$ e $w$ ma in forma esponenziale:
$
  z w &= r e^(i theta) R e^(i phi) = r R e^(i theta + i phi) = r R e^i(theta + phi) \
  z^n &= (r e^(i theta))^n = r^n e^(i n theta), forall n in NN
$

=== Radici $n$-esime di $z$

#theorem(
  title: [Radici $n$-esime di $z$],
  [
    Sia $w in CC$. Le radici $n$-esime di $w$ sono tutti gli $n$ $z in CC$ tali che $z^n = w$.
  ],
)
#proof([Siano $w = R e^(i phi)$ e $z = r e^(i theta)$. Allora \
  $
    z^n = r^n e^(n i theta) = R e^(i phi) => cases(r^n = R, n theta = phi + 2k pi\, k in ZZ)
  $
  Dunque $r = root(n, R)$ e $theta = (phi + 2k pi)/n$. Dividendo con resto $k$ per $n$, otterremo un resto $k = s n + h$, con $h = 0, 1, 2,...,n-1$. Pertanto \
  $
    theta = (phi + 2(s n + h)pi)/n = (phi + 2h pi)/n + 2 s pi => 2s pi "è eliminabile perché multiplo di" 2 pi
  $ \
  Quindi prendiamo solo $theta = (phi + 2h pi)/n$ con $h = 0, 1, 2,..., n - 1$. Dunque abbiamo $n$ radici di $w$.
])

#theorem(
  title: [Teorema fondamentale dell'algebra],
  [
    Un'equazione polinomiale del tipo: $a_n z_n + a_(n-1) z_(n-1) + ... + a_0 z_0 = 0$ con $a_n, a_(n-1), ..., a_0 in CC$ e $a_n != 0$ ammette esattamente $n$ soluzioni appartenenti a $CC$ purché ciascuna sia contata con la propria molteplicità.
  ],
) <cpl:fond>

==== Radici di 1

#grid(
  columns: 2,
  [In $RR$, esiste solo una radice $n$-esima di 1, mentre in $CC$ ne esistono $n$ per il @cpl:fond. Se le rappresentiamo sul piano di Gauss, esse si trovano sulla circonferenza unitaria e costituiscono un poligono regolare di $n$ lati.],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3, 3),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -1.5,
      y-max: 1.5,
      x-min: -1.5,
      x-max: 1.5,
      {
        for (index, root) in (
          (
            (1, 0),
            (calc.cos(calc.pi / 3), calc.sin(calc.pi / 3)),
            (calc.cos(2 * calc.pi / 3), calc.sin(2 * calc.pi / 3)),
            (-1, 0),
            (calc.cos(4 * calc.pi / 3), calc.sin(4 * calc.pi / 3)),
            (calc.cos(5 * calc.pi / 3), (calc.sin(5 * calc.pi / 3))),
          )
        ).enumerate() {
          plot.add(((0, 0), root), style: (stroke: black))
          plot.annotate({
            mark(root, 0deg, anchor: "center", symbol: "o", fill: black)
            content((root.at(0) + 0.25, root.at(1) + 0.25), $z_#(index + 1)$)
          })
        }
        plot.add(domain: (-2 * calc.pi, 2 * calc.pi), t => (
          calc.cos(t),
          calc.sin(t),
        ))
      },
    )
  }),
)

#pagebreak()

= Funzioni

Siano $A, B$ due insiemi. Una funzione $f: A -> B$ è una *legge* che associa ad ogni elemento di $A$ *uno e uno solo* di $B$. Si denota come $y = f(x)$. $A$ è detto *dominio*, mentre $B$ *codominio*.

#definition(
  title: [Immagine del dominio],
  [
    Si dice _immagine di $A$_ tramite $f$ l'insieme degli elementi di $B$ che provengono da qualche elemento di $A$. In simboli:
    $ Im(f) eq.triple f(A) := {y in B: exists x in A, y = f(x)} $
  ],
)

#definition(
  title: [Tipologie di funzioni],
  [
    Siano $A, B$ due insiemi, $f: A -> B$. $f$ si dice:
    - _iniettiva_: $forall x_1, x_2 in A, x_1 != x_2 => f(x_1) != f(x_2)$ oppure $f(x_1) = f(x_2) => x_1 = x_2$
    - _suriettiva_: $B = Im(f)$
    - _biiettiva_ (o _bigiettiva_ o _biunivoca_): $f$ è sia suriettiva che iniettiva
  ],
)
Dunque una funzione è iniettiva quando ad ogni $x$ corrisponde *una sola* $y$ ed è suriettiva quando ogni elemento del codominio è immagine di almeno un elemento del dominio.

Se $f$ è iniettiva, allora è invertibile su $f(A)$ e non su tutto $B$, ossia è ben definita la *funzione inversa* $f^(-1): f(A) -> A$. Se $f$ è biiettiva, allora è invertibile su tutto $B$. Infatti $f^(-1): B -> A$.

#definition(
  title: [Controimmagine],
  [
    Siano $f: A -> B, D subset.eq B$. Si dice _controimmagine_ (o _antiimmagine_) di D l'immagine della $f^(-1)$ con dominio $D$. In simboli:
    $ f^(-1)(D) := {x in A : f(x) in D} $
  ],
)
Un'operazione che si può svolgere tra funzioni è la *composizione*. Va notato che la composizione non è commutativa, dunque $g compose f != f compose g$.
#definition(
  title: [Funzione composta],
  [
    Siano $f: A -> B, g: B -> C$. Allora $g compose f := g[f(x)]$ dove $g compose f: A -> C$.
  ],
)

#example([
  Siano $f: A -> B, g: C -> D$ due funzioni, con $f(x) = x + 1, g(x) = x^2, A, B, C, D = RR$. \
  $g compose f: A -> D => (g compose f)(x) = g[f(x)] = (x + 1)^2$ mentre \
  $f compose g: C -> B => (f compose g)(x) = f[g(x)] = x^2 + 1$. Dunque $g compose f != f compose g$.
])

#note-box([
  Se una funzione $f: A -> B$ è iniettiva, allora:
  - $(f^(-1) compose f)(x) = f^(-1)[f(x)] = x, forall x in A$
  - $(f^(-1) compose f)(y) = f^(-1)[f(y)] = y, forall y in B$
])
#definition(
  title: [Funzione reale di una variabile reale],
  [
    Siano $A subset.eq RR, B subset.eq RR, f: A -> B$. Allora $f$ si dice _funzione reale di una variabile reale_.
  ],
)

== Insieme di definizione

In molti casi, una funzione è data da un'espressione analitica (es. $f(x) = sqrt(x + 1)$, $f(x) = log(1 - x^2)$), dunque non definendo esplicitamente dominio e codominio. Pertanto si assume che il codominio sia $RR$ e che il dominio sia l'*insieme di definizione* di $f$, ossia l'insieme di tutte le $x in RR$ tali che le operazioni che compaiono nell'espressione di $f(x)$ hanno senso. \
#example([
  $f(x) = sqrt(x - 1), " " D = { x in RR : x - 1 >= 0} = {x in RR : x >= 1} = [1; +infinity)$
])

== Funzioni monotòne
#definition(
  title: [Funzione monotona],
  [
    Siano $A subset.eq RR, f: A -> RR$. $forall x_1, x_2 in A, x_1 < x_2$, $f$ si dice:
    - _crescente_: $f(x_1) <= f(x_2)$
    - _decrescente_: $f(x_1) >= f(x_2)$
    - _strettamente crescente_: $f(x_1) < f(x_2)$
    - _strettamente decrescente_: $f(x_1) > f(x_2)$
    Dunque $f$ si dice:
    - _monotona_ se è crescente o decrescente
    - _strettamente monotona_ se è strettamente crescente o strettamente decrescente
  ],
)
#note-box([
  Se il rapporto incrementale di $f$ ($(f(x_1) + f(x_2))/(x_1 - x_2), forall x_1, x_2 in A, x_1 != x_2$) è positivo, allora $f$ è crescente. Viceversa, $f$ è decrescente.
])

== Funzioni pari e dispari

#definition(title: [Funzioni pari e dispari], [
  Sia $f: RR -> RR$. $forall x in RR, f$ si dice:
  - _pari_ se $f(x) = f(-x)$
  - _dispari_ se $f(x) -f(x)$
])
In altre parole le funzioni pari e dispari presentano una *simmetria*, le prime rispetto all'asse delle ordinate e le seconde rispetto all'origine. \
In generale, $f(x) = x^n, n in NN$ è pari per tutti gli $n$ pari e dispari per tutti gli $n$ dispari.

== Funzioni periodiche

#definition(
  title: [Funzioni periodiche],
  [
    Siano $f: RR -> RR, T in RR$. $f$ si dice _periodica di periodo $T$_ se $f(x + T) = f(x), forall x in RR$.
  ],
)
Esempi di funzioni periodiche sono le funzioni goniometriche come $sin x, cos x$ e $tan x$.

#pagebreak()

== Grafico di una funzione

#definition(title: [Grafico di $f$], [
  Sia $f:A -> B$. Allora $G_f := {(x, f(x)) : x in A}$ si dice _grafico di $f$_.
])
Se dominio e codominio di $f$ sono contenuti in $RR$, allora $G_f$ può essere rappresentato nel piano cartesiano $O x y$.

== Estremi superiore ed inferiore

#definition(title: [Funzione limitata], [
  Siano $A subset.eq RR, f: A -> RR$. $f$ si dice:
  - _limitata superiormente_ se $f(A)$ è limitato superiormente
  - _limitata inferiormente_ se $f(A)$ è limitato inferiormente

  In generale, $f$ si dice _limitata_ se è $f(A)$ è limitato.
])
#definition(
  title: [Estremi di una funzione],
  [
    Sia $f: RR -> RR$. $sup f := sup f(A), max f := max f(A), inf f := inf f(A), min f := min f(A)$.
  ],
)
== Funzioni elementari

#align(center, grid(
  columns: 3,
  gutter: 4pt,
  align: center + horizon,
  func($f(x) = x$, (4, 4), (-5, 5), (x => x,)),
  func($f(x) = x^n, \ forall n in NN$, (4, 4), (-1.2, 1.2), (
    x => calc.pow(x, 2),
    x => calc.pow(x, 3),
  )),
  func(
    $f(x) = x^(p/q), \ forall p,q in NN, p,q "coprimi",q "pari"$,
    (4, 4),
    (0, 2),
    (x => calc.root(x, 2),),
    y-min: -2,
    y-max: 2,
    x-min: -2,
    x-max: 2,
  ),

  func(
    $f(x) = x^(p/q), \ forall p,q in NN, p,q "coprimi", q "dispari"$,
    (4, 4),
    (-2, 2),
    (x => calc.root(x, 3),),
  ),
  func(
    $f(x) = x^(-p/q), \ forall p,q in NN, p,q "coprimi", q "pari"$,
    (4, 4),
    (0.001, 100),
    (x => calc.root(x + 0.05, -2),),
    y-min: -2,
    y-max: 2,
    x-min: -16,
    x-max: 16,
  ),
  func(
    $f(x) = x^(-p/q), \ forall p,q in NN, p,q "coprimi", q "dispari"$,
    (4, 4),
    (-15, 15),
    (x => calc.root(x, -3),),
  ),
))

=== Funzioni circolari

#align(center, grid(
  columns: 4,
  gutter: 4pt,
  align: center + horizon,
  func($f(x) = sin(x)$, (3, 3), (-2 * calc.pi, 2 * calc.pi), (calc.sin,)),
  func($f(x) = cos(x)$, (3, 3), (-2 * calc.pi, 2 * calc.pi), (calc.cos,)),
  func(
    $f(x) = tan(x)$,
    (3, 3),
    (-calc.pi, calc.pi),
    (calc.tan,),
    y-max: 2,
    y-min: -2,
  ),
  func(
    $f(x) = "cotan"(x)$,
    (3, 3),
    (-calc.pi, calc.pi),
    (x => calc.cos(x) / calc.sin(x),),
    y-max: 2,
    y-min: -2,
  ),

  inverseFunc($f(x) = arcsin(x)$, (3, 3), (-2 * calc.pi, 2 * calc.pi), (
    calc.sin,
  )),
  inverseFunc($f(x) = arccos(x)$, (3, 3), (-2 * calc.pi, 2 * calc.pi), (
    calc.cos,
  )),
  inverseFunc(
    $f(x) = arctan(x)$,
    (3, 3),
    (-calc.pi / 2, calc.pi / 2),
    (calc.tan,),
    x-max: 2,
    x-min: -2,
    y-max: 3,
    y-min: -3,
  ),
  inverseFunc(
    $f(x) = "arccot"(x)$,
    (3, 3),
    (0.001, calc.pi),
    (x => calc.cos(x) / calc.sin(x),),
    x-max: 2,
    x-min: -2,
    y-max: 3,
    y-min: -3,
  ),
))

=== Funzioni esponenziali e logaritmi
#align(center, grid(
  columns: 4,
  gutter: 4pt,
  align: center + horizon,
  func(
    $f(x) = a^x \ forall a in RR, a > 0$,
    (3, 3),
    (-3, 3),
    (x => calc.pow(calc.e, x),),
    x-min: -1.5,
    x-max: 1.5,
    y-min: -2,
    y-max: 2,
  ),
  func(
    $f(x) = a^x \ forall a in RR, 0 < a < 1$,
    (3, 3),
    (-3, 3),
    (x => calc.pow(1 / 2, x),),
    x-min: -1.5,
    x-max: 1.5,
    y-min: -2,
    y-max: 2,
  ),
  func(
    $f(x) = log_a (x) \ forall a in RR, a > 0$,
    (3, 3),
    (0.001, 3),
    (x => calc.ln(x),),
    x-min: -3,
    x-max: 3,
    y-min: -3,
    y-max: 3,
  ),
  func(
    $f(x) = log_a (x) \ forall a in RR, 0 < a < 1$,
    (3, 3),
    (0.001, 3),
    (x => calc.log(x, base: 1 / 2),),
    x-min: -3,
    x-max: 3,
    y-min: -3,
    y-max: 3,
  ),
))

=== Funzioni iperboliche

#align(center, grid(
  columns: 3,
  gutter: 4pt,
  align: center + horizon,
  func(
    $f(x) = sinh(x) = (e^x - e^(-x))/2$,
    (4, 4),
    (-4, 4),
    (calc.sinh,),
    y-min: -5,
    y-max: 5,
  ),
  func(
    $f(x) = cosh(x) = (e^x + e^(-x))/2$,
    (4, 4),
    (-4, 4),
    (calc.cosh,),
    y-min: -5,
    y-max: 5,
  ),
  func(
    $f(x) = tanh(x) = sinh(x) / cosh(x)$,
    (4, 4),
    (-4, 4),
    (calc.tanh,),
    y-min: -5,
    y-max: 5,
  ),
))

Sono dette *iperboliche* perché il punto $P(cosh(x_0), sinh(x_0)) in x^2 + y^2 = 1, forall x_0 in RR$, quindi ogni punto con tali coordinate appartiene all'iperbole equilatera riferita agli assi.

=== Funzioni varie

#align(center, grid(
  columns: 3,
  gutter: 4pt,
  align: center + horizon,
  func($f(x) = abs(x)$, (4, 4), (-5, 5), (calc.abs,), y-min: -3, y-max: 3),
  func($f(x) = \[x\]$, (4, 4), (-5, 5), (calc.floor,), y-min: -3, y-max: 3),
  func(
    $f(x) = "sgn"(x)$,
    (4, 4),
    (-5, 5),
    (x => if x > 0 { 1 } else if x < 0 { -1 } else { 0 },),
    y-min: -3,
    y-max: 3,
  ),
))

= Limiti di successioni

#definition(title: [Successione numerica], [
  Una successione numerica è una funzione $a_n: NN -> RR$.
])

Ogni $a_n$ è detto un *elemento della successione*, mentre la scrittura ${a_n}$ indica la successione stessa e l'insieme dei suoi elementi ($Im a_n = {a_1, a_2, ... a_n, forall n in NN}$).

#definition(
  title: [Successione limitata],
  [
    Sia ${a_n}$ una successione. Essa si dice:
    - _limitata superiormente_ $<=> exists M in RR : a_n <= M, forall n in NN$
    - _limitata inferiormente_ $<=> exists m in RR : a_n >= m, forall n in NN$
    Quindi una successione è limitata superiormente o inferiormente se anche la sua immagine lo è.
  ],
)
#definition(title: [Successione monotòna], [
  Sia ${a_n}$ una successione. Essa si dice:
  - _crescente_ se $a_n <= a_(n + 1), forall n in NN$
  - _strettamente crescente_ se $a_n < a_(n + 1), forall n in NN$
  - _decrescente_ se $a_n >= a_(n + 1), forall n in NN$
  - _strettamente decrescente_ se $a_n > a_(n + 1), forall n in NN$
  - _monotòna_ se è vera almeno una di queste condizioni
  - _strettamente monotòna_ se sono vere la seconda o la quarta condizione
])

#definition(
  title: [Estremi di una successione],
  [
    #set list(spacing: 1.065em)
    Sia ${a_n}$ una successione. Allora
    - $max {a_n} := max Im a_n := {exists n_0 in NN : a_n <= a_n_0, forall n in NN}$
    - $min {a_n} := min Im a_n := {exists n_0 in NN : a_n >= a_n_0, forall n in NN}$
    - $sup {a_n} := sup Im a_n := {exists Lambda in RR : cases(Lambda >= a_n\, forall n in NN, forall epsilon > 0 " " exists n_epsilon in NN : a_n_epsilon > Lambda - epsilon)}$
    - $inf {a_n} := inf Im a_n := {exists lambda in RR : cases(lambda <= a_n\, forall n in NN, forall epsilon > 0 " " exists n_epsilon in NN : a_n_epsilon < lambda + epsilon)}$
  ],
) <lms:est>

== Tipologie di limite

#definition(
  title: [Proprietà valida definitivamente],
  [
    Sia $P(n)$ una proprietà di $NN$. Essa _vale definitivamente_ se $exists n_0 in NN : P(n) "vera" forall n in NN, n >= n_0$.
  ],
)
#definition(
  title: [Striscia],
  [
    Sia $a,r in RR$. La _striscia_ di raggio $r$ attorno alla retta $y = a$ corrisponde a
    $ S_(a,r) = {(x, y) in RR^2 : abs(y - a) < r} $
  ],
)
La striscia corrisponde dunque all'insieme dei punti la cui distanza dalla retta vale $r$.

#definition(
  title: [Limite di successione],
  [
    Sia $l in RR$. $l$ si dice _limite della successione_ ${a_n}$ se $forall epsilon > 0 " " exists nu_epsilon in NN : abs(a_n - l) < epsilon, forall n > nu_epsilon$. Si indica come $display(lim_(n-> infinity)) a_n = l$ o $display(op(a_n -> l, limits: #true)_(n -> infinity))$.
  ],
) <lms:lms>

Se infatti consideriamo la striscia $S_(l, epsilon)$ possiamo dire la relazione $forall epsilon > 0 " " abs(a_n - l) < epsilon$ vale definitivamente, ossia sappiamo che, se il limite esiste, scegliendo un qualsiasi $epsilon > 0$ troveremo un punto $P_n(n, a_n)$ all'interno della striscia.

#theorem(title: [Unicità del limite], [
  Sia ${a_n}$ una successione. Se ${a_n}$ ammette limite, allora esso è unico.
])
#proof([
  Supponiamo, per assurdo, che $display(lim_(n-> infinity)) a_n = l_1$ e che $display(lim_(n-> infinity)) a_n = l_2$ con $l_1 != l_2$. Allora, per la @lms:lms:
  1. $forall epsilon > 0 " " exists nu_(1,epsilon) in NN : abs(a_n - l_1) < epsilon, forall n > nu_(1,epsilon)$
  2. $forall epsilon > 0 " " exists nu_(2,epsilon) in NN : abs(a_n - l_2) < epsilon, forall n > nu_(2,epsilon)$
  Siano $nu_epsilon := max{nu_(1,epsilon), nu_(2,epsilon)}, epsilon = abs(l_1 - l_2)/2 = abs(l_1 - a_n + a_n - l_2)/2$. Allora avremmo che $abs(a_n - l_1) < epsilon, forall n > nu_epsilon$ e che $abs(a_n - l_2) < epsilon, forall n > nu_epsilon$, con $nu_epsilon >= nu_(1,epsilon)$ e $nu_epsilon >= nu_(2,epsilon)$. \
  Dunque, per il @abs:dtr, $abs(l_1 - l_2) <= abs(a_n - l_1) + abs(a_n - l_2), forall n > nu_epsilon$. Ma essendo anche \
  $abs(a_n - l_1) < epsilon$ e $abs(a_n - l_2) < epsilon$, allora $abs(l_1 - l_2) < 2epsilon => abs(l_1 - l_2)/2 < epsilon$. \
  Questo è un assurdo perché $epsilon$ non può essere contemporaneamente minore ed uguale a $abs(l_1 - l_2)/2$.
])

#definition(
  title: [Successione convergente],
  [
    Sia ${a_n}$ una successione. Essa si dice _convergente_ se $display(lim_(n -> infinity) a_n) = l$ per qualche $l in RR$.
  ],
)

#theorem(
  title: [Limitatezza di una successione convergente],
  [
    Sia ${a_n}$ una successione. Se ${a_n}$ è convergente, allora è anche limitata.
  ],
)
#proof([
  ${a_n}$ convergente $<=> exists l in RR : display(lim_(n -> infinity) a_n) = l$. Supponiamo dunque $epsilon = 1$, allora, per la @lms:lms,
  $exists nu in NN : abs(a_n - l) < 1, forall n > nu$. Inoltre $abs(a_n) = abs(a_n - l + l)$, dunque, per il @abs:dtr, $abs(a_n - l + l) <= abs(a_n - l) + abs(l) < 1 + abs(l)$. Dunque, possiamo dire che $abs(a_n) <= k$ con \ $k := max{abs(a_1), abs(a_2), ..., abs(a_n), 1 + abs(l)}$, quindi ${a_n}$ è limitata.
])
=== Non esistenza del limite

Se infiniti punti di una successione non appartengono alla striscia $S_(l, epsilon), forall epsilon > 0$, allora la successione non ammette limite finito $forall l in RR$.
#warning-box([
  ${a_n}$ limitata $arrow.r.double.not {a_n}$ convergente, nonostante valga il contrario.
])
#note-box([
  Se $display(lim_(k -> infinity) a_(2k)) = l_1, display(lim_(k -> infinity) a_(2k + 1)) = l_2, l_1 != l_2 => exists.not display(lim_(n -> infinity) a_n)$.
])

=== Successioni divergenti

#definition(
  title: [Successione divergente],
  [
    Sia ${a_n}$ una successione. Essa ha limite:
    - $+infinity$ o _diverge positivamente_ se $forall M > 0 " " exists nu_m in NN : a_n > M, forall M > nu_M$
    - $-infinity$ o _diverge negativamente_ se $forall M > 0 " " exists nu_m in NN : a_n < -M, forall M > nu_M$
  ],
)

Ciò vuol dire che $forall M > 0$ i punti della successione appartengono definitivamente al semipiano soprastante alla retta $y = M$ nel caso di divergenza positiva. Viceversa, i punti appartengono definitivamente al semipiano sottostante alla retta $y = -M$ nel caso di divergenza negativa.

#definition(
  title: [Successione regolare],
  [
    Una successione si dice _regolare_ se ammette limite finito o infinito. Altrimenti, si dice _irregolare_.
  ],
)

== Algebra dei limiti

Siano ${a_n}, {b_n}$ due successioni tali che $display(lim_(n -> infinity)) a_n -> a$ e $display(lim_(n -> infinity)) b_n -> b$, con $a, b in RR$.

$
  display(lim_(n -> infinity)) (a_n + b_n) &= cases(a + b &"se" a != plus.minus infinity \, b != plus.minus infinity, plus.minus infinity &"se" b = plus.minus infinity, plus.minus infinity &"se" a = b = plus.minus infinity) \
  display(lim_(n -> infinity)) (a_n b_n) &= cases(a dot b &"se" a != plus.minus infinity \, b != plus.minus infinity, plus.minus infinity &"se" a > 0 \, b = plus.minus infinity, minus.plus infinity &"se" a < 0 \, b = plus.minus infinity, plus.minus infinity &"se" a = b = plus.minus infinity, minus infinity &"se" a = plus.minus infinity \, b = minus.plus infinity) \
  display(lim_(n -> infinity)) a_n / b_n &= cases(a / b &"se" a != plus.minus infinity \, b != plus.minus infinity, 0 &"se" b = plus.minus infinity, plus.minus infinity &"se" a = plus.minus infinity \, b > 0, minus.plus infinity &"se" a = plus.minus infinity \, b < 0, +infinity &"se" a > 0 \, b = 0 \, b_n > 0 "definitivamente", -infinity &"se" a < 0 \, b = 0 \, b_n > 0 "definitivamente", +infinity &"se" a < 0 \, b = 0 \, b_n < 0 "definitivamente", -infinity &"se" a > 0 \, b = 0 \, b_n < 0 "definitivamente", exists.not) "   con" b_n != 0 "definitivamente"
$
$
  display(lim_(n -> infinity)) (a_n)^(b_n) = cases(a^b &"se" a > 0, 0 &"se" 0 <= a < 1\, b = +infinity, +infinity &"se" 0 <= a < 1\, b = -infinity, +infinity &"se" a > 1\, b = +infinity, 0 &"se" a > 1\, b = -infinity, +infinity &"se" a = +infinity\, b > 0, 0 &"se" a = +infinity\, b < 0, +infinity &"se" a = +infinity\, b = +infinity, 0 &"se" a = +infinity\, b = -infinity) "con" a_n >= 0 "definitivamente"
$

Alcuni casi sono stati esclusi dal momento che non si possono determinare con certezza. Sono le cosiddette *forme indeterminate*, ossia $infinity - infinity), 0 dot (plus.minus infinity), 0 / 0, (plus.minus infinity) / (plus.minus infinity), 0^0, 1^(plus.minus infinity), infinity^0$.

#theorem(
  title: [Limite della somma di successioni],
  [
    Siano ${a_n}, {b_n}$ due successioni. Se $display(lim_(n -> infinity)) a_n = a$ e $display(lim_(n -> infinity)) b_n = b$ con $a, b in RR$ allora \ $ display(lim_(n -> infinity)) (a_n + b_n) = a + b $.
  ],
)
#proof([
  $forall epsilon > 0 " " exists nu_(1, epsilon) in NN : abs(a_n - a) < epsilon " " forall n > nu_(1,epsilon), exists nu_(2, epsilon) in NN : abs(b_n -b) < epsilon " " forall n > nu_(2, epsilon)$ \
  $nu_epsilon := max{nu_(1, epsilon), nu_(2, epsilon)} => forall epsilon > 0, forall n > nu_epsilon " " abs(a_n + b_n - (a + b)) = abs((a_n - a) + (b_n - b))$ \
  Per il @abs:dtr, $abs((a_n - a) + (b_n - b)) <= abs(a_n - a) + abs(b_n - b) < epsilon + epsilon$ \
  $display(op(<=>, limits: #true)^"def.") forall epsilon > 0 " " exists nu_epsilon in NN : abs((a_n + b_n) - (a + b)) < epsilon => display(lim_(n -> infinity)) (a_n + b_n) = a + b$
])
#theorem(
  title: [Permanenza del segno],
  [
    Sia ${a_n}$ una successione con $display(lim_(n -> infinity)) a_n = a$. Allora $exists nu in NN$ tale che se:
    - $a > 0 => a_n > 0 " " forall n > nu$
    - $a < 0 => a_n < 0 " " forall n > nu$
  ],
) <lms:prm>
#proof([
  Per la @lms:lms, $forall epsilon > 0 " " exists nu_epsilon in NN : abs(a_n - a) < epsilon, forall n > nu_epsilon$ \ $=> a - epsilon < a_n < a + epsilon$. \ Scegliamo allora $epsilon = a/2$, il quale è un numero positivo. Allora \
  $a - a/2 < a_n < a + a/2 <=> a/2 < a_n < 3/2 a => a_n > 0$ definitivamente.
])
#corollary([
  Se $display(lim_(n -> infinity)) a_n = a, a_n >= 0 " " forall n in NN$ allora $a >= 0$. Invece se $a_n <= 0$ allora $a <= 0$.
])
#proof([
  Supponiamo, per assurdo, che $a < 0$. Allora, per il @lms:prm si avrebbe $a_n < 0$ definitivamente, il che è un assurdo.
])
#corollary(
  title: [Proprietà del confronto],
  [
    Se $display(lim_(n -> infinity)) a_n = a, display(lim_(n -> infinity)) b_n = b, a_n >= b_n, forall n in NN$ allora $a >= b$.
  ],
) <lms:cprm>
#proof([
  $c_n := a_n - b_n => c_n >= 0 " " forall n in NN$. Secondo l'algebra dei limiti, $display(lim_(n -> infinity)) c_n = a - b$. \
  Grazie al @lms:cprm $display(lim_(n -> infinity)) c_n >= 0 => a - b >= 0 => a >= b$.
])
#theorem(
  title: [Teorema dei due carabinieri],
  [
    Siano ${a_n}, {b_n}, {c_n}$ tre successioni con $a_n <= c_n <= b_n, forall n in NN$. Se $display(lim_(n -> infinity)) a_n = display(lim_(n -> infinity)) b_n = l$ allora $display(lim_(n -> infinity)) c_n = l$.
  ],
) <lms:tdc>
#proof([
  Per la @lms:lms, $forall epsilon > 0 #" " exists nu_(1, epsilon) in NN : abs(a_n - l) < epsilon " " forall n > nu_(1, epsilon)$, \ $exists nu_(2, epsilon) in NN : abs(b_n - l) < epsilon " " forall n > nu_(2, epsilon)$. \
  $nu_epsilon := max{nu_(1,epsilon), nu_(2,epsilon)}$. Allora $forall n > nu_epsilon " " l - epsilon < a_n < l + epsilon, l - epsilon < b_n < l + epsilon$ \
  $=> l - epsilon < a_n <= c_n <= b_n < l + epsilon$ per ipotesi. $=> l - epsilon < c_n < l + epsilon " " forall n > nu_epsilon display(op(<=>, limits: #true)^"def.") exists display(lim_(n -> infinity)) c_n = l$.
])
#note-box([
  Se $a_n <= b_n " " forall n in NN$ e $display(lim_(n -> infinity)) a_n = +infinity$ allora $display(lim_(n -> infinity)) b_n = +infinity$. \
  Se invece $display(lim_(n -> infinity)) b_n = -infinity$ allora $display(lim_(n -> infinity)) a_n = -infinity$.
])
#definition(
  title: [Successione infinitesima],
  [
    Sia ${a_n}$ una successione. Essa si dice _infinitesima_ se $display(lim_(n -> infinity)) a_n = 0$.
  ],
)
#lemma(title: [Limite del valore assoluto di una successione infinitesima], [
  Sia ${a_n}$ una successione. Allora $display(lim_(n -> infinity)) a_n = 0 <=> display(lim_(n -> infinity)) abs(a_n) = 0$
]) <lms:lmp>
#proof([
  Sia ${b_n}$ una successione tale che $display(lim_(n -> infinity)) b_n = 0$. Dunque, per la @lms:lms \
  $forall epsilon > 0 " " exists nu_epsilon in NN : abs(b_n) < epsilon, forall n > nu_epsilon$. Se consideriamo $b_n = abs(a_n)$ allora $abs(b_n) = abs(abs(a_n)) = abs(a_n)$ \
  $<=> display(lim_(n -> infinity)) a_n = 0$
])
#theorem(
  title: [Limite del prodotto di successioni],
  [
    Siano ${a_n}, {b_n}$ una successione limitata e una successione infinitesima. Allora $display(lim_(n -> infinity)) (a_n b_n) = 0$.
  ],
)
#proof([
  Per il @lms:lmp $display(lim_(n -> infinity)) abs(b_n) = 0$. \
  $abs(a_n b_n) >= 0 <=> abs(a_n)abs(b_n) >= 0, forall n in NN$. Visto che $display(lim_(n -> infinity)) = M => abs(a_n) <= M <=> abs(a_n)abs(b_n) <= underbrace(M abs(b_n), -> 0)$ \
  $=> 0 <= abs(a_n b_n) = abs(a_n)abs(b_n) <= M abs(b_n).$ Per il @lms:tdc, $display(lim_(n -> infinity)) (a_n b_n) = 0$.
])
#theorem(
  title: [Regolarità delle successioni monotone],
  [
    Ogni successione monotona ammette limite. Inoltre, se ${a_n}$ è una successione, allora \ $ display(lim_(n -> infinity)) a_n = cases(sup{a_n} &"se" {a_n} arrow.tr, inf{a_n} &"se" {a_n} arrow.br) $
  ],
) <lms:reg>
#proof([
  Supponiamo che ${a_n} arrow.tr$ e limitata superiormente. Poniamo $lambda := sup{a_n} in RR$. \
  Per la @lms:est, $forall epsilon > 0 " " exists nu in NN : lambda - epsilon < a_n$. Poiché ${a_n} arrow.tr$ allora $a_n >= a_nu, forall n > nu$. \
  Dunque $lambda - epsilon < a_nu <= a_n <= lambda < lambda + epsilon, forall n > nu display(op(<=>, limits: #true)^"def.") display(lim_(n -> infinity)) a_n = lambda$. \
  Supponiamo che ${a_n} arrow.br$ e illimitata superiormente. \
  $<=> forall M > 0 " " exists nu in NN : a_nu > M, forall n > nu " " a_n >= a_nu => a_n >= a_nu > M <=> display(lim_(n -> infinity)) a_n = +infinity$.
])

=== Limiti notevoli

- *Esponenziale*
$
  display(lim_(n -> infinity)) a^n = cases(+infinity &"se" a > 1, 1 &"se" a = 1, 0 &"se" -1 < a < 1, exists.not &"se" a <= -1)
$
#proof([
  Per il @ind:brn, $(1 + x)^n >= 1 + n x, forall x >= 1 forall n in NN$ \
  - $a > 1$: $x = a - 1 => a^n >= 1 + n(a - 1), display(lim_(n -> infinity)) (1 + n(a - 1)) = +infinity$ \ #"          " Per il @lms:cprm, $display(lim_(n -> infinity)) a_n$
  - $a = 1$: $1^n = 1, forall n in NN <=> display(lim_(n -> infinity)) 1^n = 1$
  - $-1 < a < 1$: $abs(a^n) = abs(a)^n = 1/underbrace((1/abs(a))^n, -> 1) => display(lim_(n -> infinity)) a^n = 0$
  #set par(leading: 2em)
  - $a = 0$: $0^n = 0, forall n in NN => display(lim_(n -> infinity)) 0^n = 0$
  - $a <= -1$: $cases(display(lim_(k -> infinity)) a^(2k) &= cases(1 &"se" a = -1, -infinity &"se" a < -1), display(lim_(k -> infinity)) a^(2k + 1) &= cases(-1 &"se" a = -1, -infinity &"se" a < -1), reverse: #true) => exists.not display(lim_(n -> infinity)) a_n$
])
- *Radici*
$
  display(lim_(n -> infinity)) root(n, a) = 1, display(lim_(n -> infinity)) root(n, a^b) = 1 "con" b in RR
$
#proof([
  - $a > 1$: Sia $b_n := root(n, a) - 1$, dunque $b_n >= 0, forall n in NN$ \ #"          " Per il @ind:brn, $(1 + b_n)^n >= 1 + b_n n => (root(n, a))^n >= 1 + b_n n$ \ #"          " $<=> a >= 1 + b_n n => 0 <= b_n <= (a - 1)/n$ \ #"          " Per il @lms:tdc, $display(lim_(n -> infinity)) b_n = 0 => display(lim_(n -> infinity)) root(n, a) = 1$
  #set par(leading: 1em)
  - $0 < a < 1$: $root(n, a) = 1 / underbrace(root(n, 1 / a), -> 1) -> 1 / 1 => display(lim_(n -> infinity)) root(n, a) = 1$
])
- *Funzioni goniometriche* dove ${a_n}$ è una successione tale che $display(lim_(n -> infinity)) a_n = 0$
$
  display(lim_(n -> infinity)) sin(a_n) = 0&, display(lim_(n -> infinity)) cos(a_n) = 1 \ display(lim_(n -> infinity)) sin(a_n) / a_n = 1&, display(lim_(n -> infinity)) (1 - cos(a_n))/a_n^2 = 1/2
$
#proof([
  #grid(
    columns: 2,
    [
      #set par(leading: 1.065em)
      Prima di tutto dimostriamo che $cos x < (sin x) / x < tan x$ se $0 < abs(x) <= pi/2$. \
      $overline(A B) = 1, overline(B C) =: x, overline(C E) = sin x, overline(B D) = tan x$ \
      $=> A_(Delta A B C) = (sin x)/2, A_(Delta A B D) = (tan x)/2, A_accent(A B C, paren.t) = x / 2$ \
      $=> Delta A B C subset accent(A B C, paren.t) subset Delta A B D$ \
      $=> (sin x) / 2 < x / 2 < (tan x) / 2 display(op(=>, limits: #true)_(dot 2/(sin x))) 1 < x / (sin x) < 1 / (cos x) display(op(=>, limits: #true)_(x^-1)) cos x < (sin x) / x < 1$
    ],
    cetz.canvas({
      import cetz.draw: *
      import cetz-plot: plot
      plot.plot(
        size: (3, 3),
        axis-style: "school-book",
        x-tick-step: none,
        y-tick-step: none,
        y-min: -0.5,
        y-max: 1,
        x-min: -0.5,
        x-max: 1,
        {
          let letters = ("A", "B", "C", "D", "E")
          for (index, root) in (
            (0, 0),
            (1, 0),
            (calc.cos(calc.pi / 4), calc.sin(calc.pi / 4)),
            (1, calc.tan(calc.pi / 4)),
            (calc.cos(calc.pi / 4), 0),
          ).enumerate() {
            plot.annotate({
              mark(
                root,
                0deg,
                anchor: "center",
                symbol: (symbol: "o", scale: 0.6),
                fill: black,
              )
              content((root.at(0) + 0.15, root.at(1) + 0.15), letters.at(index))
            })
          }
          plot.add(domain: (-2 * calc.pi, 2 * calc.pi), t => (
            calc.cos(t),
            calc.sin(t),
          ))
          plot.add(((0, 0), (1, calc.tan(calc.pi / 4))))
          plot.add(
            (
              (calc.cos(calc.pi / 4), calc.sin(calc.pi / 4)),
              (calc.cos(calc.pi / 4), 0),
            ),
            style: (stroke: (dash: "dashed", paint: red)),
          )
          plot.add(((1, calc.tan(calc.pi / 4)), (1, 0)), style: (
            stroke: (dash: "dashed", paint: red),
          ))
        },
      )
    }),
  ) \ \

  1. Sapendo che $cos(a_n) >= -1$ allora $-1 <= cos(a_n) < sin(a_n) / a_n < 1 => abs(sin(a_n)/a_n) < 1$ \
  #"   " $<=> abs(sin(a_n)) < underbrace(abs(a_n), -> 0)$. Dunque, per il @lms:tdc, $display(lim_(n -> infinity)) abs(sin(a_n)) = 0$ \
  #"   " Quindi, per il @lms:lmp $=> display(lim_(n -> infinity)) sin(a_n) = 0$.
  2. Poiché $0 < cos(a_n) <= 1$ definitivamente, allora $0 <= 1 - cos(a_n)$. Inoltre \
  #"   " $1 - cos(a_n) = (1 - cos(a_n)) dot (1 + cos(a_n))/(1 + cos(a_n)) = (1 - cos^2 (a_n))/(1 + cos(a_n)) = (sin^2 (a_n))/(1 + cos(a_n))$. Poiché $1 + cos(a_n) > 1$ allora \
  #"   " $(sin^2 (a_n))/(1 + cos(a_n)) < sin^2 (a_n)$. \
  #"   " Per il @lms:tdc, $display(lim_(n -> infinity)) (1 - cos(a_n)) = 0 <=> display(lim_(n -> infinity)) cos(a_n) = 1$.
  3. Poiché $underbrace(cos(a_n), -> 1) < sin(a_n)/a_n < 1$, allora, per il @lms:tdc, $display(lim_(n -> infinity)) sin(a_n)/a_n = 1$.
  4. $(1 - cos(a_n))/a^2_n = (1 - cos(a_n))/a^2_n dot (1 + cos(a_n))/(1 + cos(a_n)) = (1 - cos^2 (a_n))/(a^2_n (1 + cos(a_n))) = (sin^2 (a_n))/(a^2_n (1 + cos(a_n))) = underbrace((sin(a_n)/(a_n))^2, -> 1) 1 / underbrace(1 + cos(a_n), -> 2)$ \
  #"   " $=> display(lim_(n -> infinity)) (1 - cos(a_n))/(a^2_n) = 1/2$.
])

- *Logaritmi ed esponenziali*
$
  display(lim_(n -> infinity)) log(1 + a_n)/a_n = 1, display(lim_(n -> infinity)) (e^(a_n) - 1)/a_n = 1 "con" display(lim_(n -> infinity)) a_n = 0
$
#proof([
  1. $log(1 + a_n)/a_n = 1/a_n log(1 + a_n) = log(1 + a_n)^(1/a_n)$. Sia ora $b_n := 1/a_n$, dunque $display(lim_(n -> infinity)) b_n = 0$. \
  #"   " $<=> display(lim_(n -> infinity)) log(underbrace((1 + 1/b_n)^(b_n), -> e)) = log e = 1$
  2. Sia $c_n := e^(a_n) - 1$, dunque $display(lim_(n -> infinity)) c_n = 0$. Poiché il limite precedente vale per una qualsiasi $a_n$\
  #"   " $log(1 + c_n)/c_n = log(cancel(1) + e^(a_n) - cancel(1))/a_n = a^n / (e^(a_n) - 1)$. Dunque $(e^(a_n) - 1)/a_n = 1 / underbrace(a_n / (e^(a_n) - 1), -> 1) => display(lim_(n -> infinity)) (e^(a_n) - 1)/a_n = 1$
])
- *Vari limiti notevoli*
$
  display(lim_(n -> infinity)) (1 + alpha / a_n)^(a_n) = e^alpha "con" alpha in RR, display(lim_(n -> infinity)) a_n = plus.minus infinity \
  display(lim_(n -> infinity)) ((1 + a_n)^alpha - 1)/a_n = alpha, display(lim_(n -> infinity)) (1 + a_n)^(1/a_n) = e "con" alpha in RR, display(lim_(n -> infinity)) a_n = 0
$

=== Rapporti tra polinomi

Siano $P(n) = a_k n^k + a_(k - 1) n^(k - 1) + ... + a_0, Q(n) = b_h n^h + b_(h - 1) n^(h - 1) + ... + b_0$ due polinomi con $a_k != 0, b_h != 0$. Allora $display(lim_(n -> infinity)) P(n) / Q(n) = infinity/infinity$, ossia una forma indeterminata. Dunque
$
  P(n) / Q(n) = (n^k (a_k + (a_(k - 1))/n + ... + (a_0)/n^k))/(n^h (b_h + (b_(h - 1))/n + ... + (b_0)/n^h)) \
  => display(lim_(n -> infinity)) P(n) / Q(n) = cases(+infinity &"se" k > h\, (a_k)/(b_h) > 0, -infinity &"se" k > h\, (a_k)/(b_h) < 0, (a_k)/(b_h) &"se" k = h, 0 &"se" k < h)
$

=== Rapporti tra infiniti
#theorem(
  title: [Criterio di rapporto per le successioni],
  [
    Siano $a_n > 0, b_n := a_(n + 1) / a_n$. Se esiste il limite $b$ di $b_n$ per $n -> infinity$ e $b < 1$, allora $display(lim_(n -> infinity)) a_n = 0$.
  ],
) <lms:crs>
#proof([
  Per il @lms:prm, $exists nu in NN : b_n < 1, forall n > nu$ Dunque $a_(n + 1) / a_n < 1, forall n > nu$ \ $display(op(<==>, limits: #true)_(a_n > 0)) a_(n + 1) < a_n, forall n > nu <=> {a_n}$ definitivamente decrescente. \
  Per il @lms:reg, $exists display(lim_(n -> infinity)) a_n := a$. Per il @lms:prm, $a >= 0$. \
  Supponiamo, per assurdo, che $a != 0$. Si avrebbe $display(lim_(n -> infinity)) b_n = display(lim_(n -> infinity)) a_(n + 1) / a_n = a / a = 1$, il che è un assurdo poiché $display(lim_(n -> infinity)) b_n < 1$ per ipotesi. Dunque $a = 0$.
]) \ \
Siano $alpha, a, b in RR, b > 0, alpha > 1$. Allora
$
  display(lim_(n -> infinity)) n^b / alpha^n &= 0 "poiché" alpha^n -> +infinity "prima di" n^b \
  display(lim_(n -> infinity)) alpha^n / n! &= 0 "poiché" n! -> +infinity "prima di" alpha^n \
  display(lim_(n -> infinity)) n! / n^n &= 0 "poiché" n^n -> +infinity "prima di" n! \
  display(lim_(n -> infinity)) log_a (n) / n^b &= 0 "poiché" n^b -> +infinity "prima di" log_a (n), "con" a > 0, a != 1, b > 0
$
#proof([
  1. $b_n := a_(n + 1) / a_n = (n + 1)^b / alpha^(n + 1) dot 1 / (n^b / alpha^n) = (n + 1)^b/(alpha^(n + 1)) dot alpha^n / n^b = underbrace(((n + 1) / n)^b, -> 1) dot 1 / alpha => display(lim_(n -> infinity)) b_n = 1 / alpha = b$. Poiché $b < 1$, allora, per il @lms:crs, $display(lim_(n -> infinity)) a_n = 0$
  #set par(leading: 1.9em)
  2. $b_n := a_(n + 1) / a_n = alpha^(n + 1) / (n + 1)! dot 1 / (alpha^n / n!) = alpha^(n + 1) / (n + 1)! dot n! / alpha^n = alpha dot n! / ((n + 1)n!) = underbrace(alpha / (n + 1), -> 0) => display(lim_(n -> infinity)) b_n = 0 => display(lim_(n -> infinity)) a_n = 0$
  3. $b_n := a_(n + 1) / a_n = (n + 1)! / (n + 1)^n dot n^n / n! = (cancel((n + 1))cancel(n!)) / cancel(n!) dot n^n / ((n + 1)^n cancel((n + 1))) = (n / (n + 1))^n = 1 / ((n + 1) / n)^n = 1 / underbrace((1 + 1 / n)^n, -> e) => display(lim_(n -> infinity)) b_n = 1 / e$ \ $=> display(lim_(n -> infinity)) a_n = 0$
  #set par(leading: 1em)
  4. Se $a > 1$: Per il @ind:brn, $(1 + t)^n >= 1 + n t, forall t in RR, forall n in NN$ \
  #"                    " $2^x >= 2^[x], forall x > 0 => (1 + 1)^[x] >= 1 + [x] >= x$. Inoltre \
  #"                    " $log_a (x) < log_a (2^x), log_a (2^x) = x log_a (2)$. Se $x = n^(b/2) => log_a (n^(b/2)) < n^(b/2) log_a (2)$ \
  #"                    " $=> (log_a (n))/n^(b/2) < 2 / b log_a (2)$. $(log_a (n))/(n^b) = 1 / n^(b/2) (log_a (n))/n^(b/2) => (log_a (n))/n^(b/2) 1 / n^(b/2) < 2 / b log_a (n) 1 / n^(b/2)$. \
  #"                    " Se $n >= 2$, allora $0 < (log_a (n))/n^(b/2) 1 / n^(b/2)< underbrace(2 / b log_a (2) 1 / n^(b/2), -> 0)$. Per il @lms:tdc, $display(lim_(n -> infinity)) a_n = 0$.
])

#pagebreak()

== Confronti e stime asintotiche

#definition(
  title: [Ordini di infiniti],
  [
    Siano ${a_n}, {b_n}$ due successioni divergenti, con $b_n != 0$ definitivamente. Allora:
    - Se $display(lim_(n -> infinity)) a_n / b_n = plus.minus infinity$ allora $a_n$ è un _infinito di ordine superiore_ rispetto a $b_n$
    - Se $display(lim_(n -> infinity)) a_n / b_n = 0$ allora $a_n$ è un _infinito di ordine inferiore_ rispetto a $b_n$
    - Se $display(lim_(n -> infinity)) a_n / b_n = l$ con $l in RR, l != 0$ allora $a_n$ e $b_n$ sono _infiniti dello stesso ordine_
    - Se $exists.not display(lim_(n -> infinity)) a_n / b_n$ allora $a_n$ e $b_n$ sono _non paragonabili_

    In notazione, $a_n succ b_n$ indica che $a_n$ è un infinito di ordine superiore rispetto a $b_n$.
  ],
)
#definition(
  title: [Ordini di infinitesimi],
  [
    Siano ${a_n}, {b_n}$ due successioni infinitesime, con $b_n != 0$ definitivamente. Allora:
    - Se $display(lim_(n -> infinity)) a_n / b_n = 0$ allora $a_n$ è un _infinitesimo di ordine superiore_ rispetto a $b_n$
    - Se $display(lim_(n -> infinity)) a_n / b_n = plus.minus infinity$ allora $a_n$ è un _infinitesimo di ordine inferiore_ rispetto a $b_n$
    - Se $display(lim_(n -> infinity)) a_n / b_n = l$ con $l in RR, l != 0$ allora $a_n$ e $b_n$ sono _infinitesimi dello stesso ordine_
    - Se $exists.not display(lim_(n -> infinity)) a_n / b_n$ allora $a_n$ e $b_n$ sono _non paragonabili_
  ],
)

#definition(
  title: [Equivalenza asintotica],
  [
    Siano ${a_n}, {b_n}$ due successioni. Se $display(lim_(n -> infinity)) a_n / b_n = 1$ allora $a_n$ è _asintotica_ o _asintoticamente equivalente_ a $b_n$. Tale relazione si indica $a_n tilde b_n$.
  ],
)
#definition(
  title: [O-piccolo],
  [
    Siano ${a_n}, {b_n}$ due successioni. ${a_n}$ è un _o-piccolo_ di ${b_n}$ se $display(lim_(n -> infinity)) a_n / b_n = 0$, ossia $a_n = o(b_n)$.
  ],
)

Se consideriamo le successioni $n^n, n!, alpha^n, n^b, log_a (n)$ con $alpha > 1, a > 1, b > 0$, allora si può dire che
$
  n^n succ n! succ alpha^n succ n^b succ log_a (n) \
  log_a (n) = o(n^b), n^b = o(alpha^n), alpha^n = o(n!), n! = o(n^n)
$

L'equivalenza asintotica possiede le seguenti proprietà:
- *riflessione*: $a_n tilde a_n$
- *transitività*: $a_n tilde b_n, b_n tilde c_n => a_n tilde c_n$
- *simmetria*: $a_n tilde b_n <=> b_n tilde a_n$
In virtù di queste tre proprietà, l'equivalenza asintotica è una *relazione di equivalenza*. Inoltre possiede queste altre proprietà:
- $a_n tilde b_n <=> a_n = b_n + o(b_n)$
- $a_n tilde a_n ', b_n tilde b_n ' => a_n b_n tilde a_n ' b_n '$
- $a_n tilde a_n ', b_n tilde b_n ' => a_n / b_n tilde (a_n ') / (b_n '),$ con $b_n != 0, b_n ' != 0$ definitivamente
- $a_n -> a_n ', alpha in RR => a_n^alpha tilde (a_n ')^alpha$ \ \
#warning-box([
  L'equivalenza non si conserva in tutti i casi, in particolare:
  - Somma: $a_n tilde a_n ', b_n tilde b_n ' arrow.r.double.not (a_n + b_n) tilde (a_n ' + b_n ')$
  - Esponenziale: $a_n tilde a_n ' arrow.r.double.not e^(a_n) tilde e^(a_n ')$
  - Logaritmi: $a_n tilde a_n ' arrow.r.double.not log(a_n) tilde log(a_n ')$
  - Elevazione a potenza: $a_n tilde a_n ', b_n tilde b_n ' arrow.r.double.not a_n^(b_n) tilde (a_n ')^(b_n ')$
  - Annullamento: $a_n tilde b_n arrow.r.double.not a_n - b_n tilde 0$ oppure $display(lim_(n -> infinity)) (a_n - b_n) = 0 arrow.r.double.not a_n - b_n tilde 0$

  In realtà, l'asintoticità si conserva nel caso dei logaritmi, ma solo se $display(lim_(n -> infinity)) a_n != 1, display(lim_(n -> infinity)) a_n ' != 1$.
])

L'o-piccolo possiede le seguenti proprietà:
- $o(a_n) = o(-a_n) = -o(a_n)$
- $co(a_n) = o(c a_n) = o(a_n), forall c in RR \\ {0}$
- $a_n o(b_n) = o(a_n b_n)$
- $o(a_n) + o(b_n) = o(a_n)$ se $a_n succ b_n$ oppure se $a_n$ è un infinitesimo di ordine inferiore rispetto a $b_n$

In virtù di questo, i limiti notevoli si possono riformulare in una forma alternativa, con ${a_n}$ infinitesima:
$
      sin(a_n) tilde a_n & => sin(a_n) = a_n + o(a_n)     \
   e^(a_n) - 1 tilde a_n & => e^(a_n) = a_n + o(a_n)      \
  log(1 + a_n) tilde a_n & => log(1 + a_n) = a_n + o(a_n) \
         "e così via..."                                  \
$
#note-box([
  È possibile sfruttare l'equivalenza asintotica anche per calcolare i limiti di funzioni composte, partendo dalla funzione più esterna.
])
#example([
  $display(lim_(n -> infinity)) (e^sin(log(1 + 1/n)) - 1) / (1/n)$. Sia $a_n := e^sin(log(1 + 1/n)) - 1$. \
  Allora $a_n tilde sin(log(1 + 1/n)) tilde log(1 + 1/n) tilde 1/n => a_n tilde 1/n$. Dunque $display(lim_(n -> infinity)) a_n / (1/n) = cancel(1/n) / cancel(1/n) = 1$
])

= Serie numeriche

Consideriamo due successioni ${a_n}, {s_n}$ tali per cui $s_1 = a_1, s_2 = a_1 + a_2, s_3 = a_1 + a_2 + a_3, ...$, quindi, in generale, $s_n = s_(n - 1) + a_n = display(sum^n_(k = 1)) a_k$. ${s_n}$ è una *serie numerica* di termine generale $a_n$. Allora $display(lim_(n -> infinity)) s_n = display(lim_(n -> infinity)) display(sum^n_(k = 1)) = display(sum^infinity_(k = 1)) a_k$, scrittura detta *somma della serie* o più comunemente *serie*. Se tale limite esiste e vale un certo $l$, allora se $l in RR$ la serie si dice *convergente*, se $l = plus.minus infinity$ si dice *divergente* (*positivamente* o *negativamente*), e se $l$ non esiste allora si dice *indeterminata*. Se la serie converge o diverge allora è detta *regolare*. Il *carattere* di una serie è la sua qualità di essere convergente, divergente o indeterminata.

Esistono casi in cui, data una successione ${a_n}$, la serie ${s_n}$ può essere espressa da una formula:
- *Serie di Mengoli*: converge a $1$
$
  a_k = 1/k - 1/(k + 1) => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) (1/k - 1/(k + 1)) = underbracket(1 - cancel(1/2), k = 1) + underbracket(cancel(1/2) - cancel(1/3), k = 2) + underbracket(cancel(1/3) - 1/4, k = 3) + ... = 1
$
- *Serie telescopica*: se $display(lim_(n -> infinity)) b_k = 0$ converge a $-b_1$
$
  a_k = b_(k + 1) - b_k => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) (b_(k + 1) - b_k) = cancel(b_2) - b_1 + cancel(b_3) - cancel(b_2) + b_4 - cancel(b_3) + ... = -b_1
$
- *Serie armonica generalizzata*: se $alpha > 1$ converge, se invece $0 < alpha <= 1$ diverge
$
  alpha = 1, a_k = 1/k^alpha => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) 1/k^alpha = 1 + 1/2 + 1/3 + 1/4 + ...
$
- *Serie geometrica*: il suo risultato dipende da una certa $x in RR$ detta *ragione*
$
  a_k = x^k, x != 1 => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) x^k = x + x^2 + x^3 + x^4 + ... = (1 - x^(n + 1)) / (1 - x) \
  => display(lim_(n -> infinity)) s_n = cases(exists.not &"se" x <= -1, 1 / (1 - x) &"se" -1 < x < 1, +infinity &"se" x >= 1)
$

#theorem(title: [Condizione necessaria per la convergenza di una serie], [
  $display(sum^infinity_(k = 1)) a_k$ convergente $=> display(lim_(n -> infinity)) a_k = 0$
])
#proof([
  Sia $display(lim_(n -> infinity)) s_n =: s$, con $s in RR$ poiché ${s_n}$ convergente per ipotesi. \
  $s_n = s_(n - 1) + a_n <=> a_n = s_n - s_(n - 1)$. In questo caso $display(lim_(n -> infinity)) s_n = s$ e $display(lim_(n -> infinity)) s_(n - 1) = s$. \
  $=> display(lim_(n -> infinity)) a_n = display(lim_(n -> infinity)) (s_(n - 1) - s_n) = s - s = 0$.
])
#warning-box([
  $display(lim_(n -> infinity)) a_n = 0 arrow.r.double.not display(sum^infinity_(k = 1)) a_k$ convergente.
])

#proposition(title: [Proprietà di una serie], [
  - Se $display(sum^infinity_(k = 1)) a_k$ e $display(sum^infinity_(k = 1))$ sono regolari e la somma $display(sum^infinity_(k = 1)) a_k + display(sum^infinity_(k = 1)) b_k$ ha significato, allora \ $display(sum^infinity_(k = 1)) (a_k + b_k) = display(sum^infinity_(k = 1)) a_k + display(sum^infinity_(k = 1)) b_k$.
  - Se $display(sum^infinity_(k = 1)) a_k$ è regolare, allora $display(sum^infinity_(k = 1)) c a_k = c display(sum^infinity_(k = 1)) a_k, forall c in RR$.
])
#theorem(title: [Carattere di una serie a termini non negativi], [
  Una serie $display(sum^infinity_(k = 1)) a_k$ con $a_k >= 0, forall k in NN$ è convergente o divergente positivamente.
])
#proof([
  Sia $s_n := display(sum^n_(k = 1)) a_k$. Dunque $s_n = a_1 + a_2 + ... + a_n$ e $s_(n + 1) = a_1 + ... + a_n + a_(n + 1)$ \
  $=> s_(n + 1) >= s_n$. Poiché $a_k >= 0, forall k in NN => s_n$ crescente. \
  Per il @lms:reg, $exists display(lim_(n -> infinity)) s_n$, il quale può essere un certo $l in RR$ oppure $+infinity$.
])

#theorem(title: [Criterio del confronto di serie], [
  Siano ${a_n}, {b_n}$ due successioni tali che $0 <= a_n <= b_n, forall n in NN$. Allora:
  #set par(leading: 2em)
  - $display(sum^infinity_(k = 1)) b_k$ convergente $=> display(sum^infinity_(k = 1)) a_k$ convergente
  - $display(sum^infinity_(k = 1)) a_k$ divergente $=> display(sum^infinity_(k = 1)) b_k$ divergente
]) <srs:cfr>
#proof([
  Siano $s_n := display(sum^infinity_(k = 1)) a_k, t_n := display(sum^infinity_(k = 1)) b_k$. $a_k <= b_k, forall k in NN => s_n <= t_n, forall n in NN$. \
  Poiché $a_k >= 0, b_k >= 0, forall k in NN => s_n, t_n$ crescenti. \
  Per il @lms:reg $exists display(lim_(n -> infinity)) s_n = s, display(lim_(n -> infinity)) t_n = t$. Dunque:
  - $t_n$ convergente $=> t in RR$ \
    Poiché $s_n <= t_n$, per il @lms:cprm $=> s <= t => s in RR => s_n$ convergente
  - $s_n$ divergente $=> s = +infinity$ \
    Poiché $s_n <= t_n$, per il @lms:cprm $=> s <= t => t = +infinity => t_n$ divergente
])
#theorem(title: [Criterio del confronto asintotico], [
  Siano ${a_n}, {b_n}$ due successioni tali che $a_n >= 0, b_n > 0, forall n in NN$ e $display(lim_(n -> infinity)) a_n / b_n = l$, con $l in [0; + infinity]$:
  #set par(leading: 2em)
  - $display(sum^infinity_(k = 1)) b_k$ convergente e $l in [0; +infinity) => display(sum^infinity_(k = 1)) a_k$ convergente
  - $display(sum^infinity_(k = 1)) b_k$ divergente e $l in (0; +infinity] => display(sum^infinity_(k = 1)) a_k$ divergente
])
#proof([
  Per definizione, $display(lim_(n -> infinity)) a_n / b_n <=> forall epsilon > 0 " " exists nu_epsilon in NN : abs(a_n / b_n - l) < epsilon, forall n > nu_epsilon$ \
  $<=> l - epsilon < a_n / b_n < l + epsilon, forall n > nu_epsilon$. Poiché $b_n > 0 => b_n (l - epsilon) < a_n < b_n (l + epsilon), forall n > nu_epsilon$.
  - Se $display(sum^infinity_(k = 1)) b_k$ converge, allora, grazie alla relazione $a_n < b_n (l + epsilon)$, per il @srs:cfr $display(sum^infinity_(k = 1)) a_k$ converge
  - Sia $l in (0; +infinity)$. Scegliamo $epsilon = l/2 => a_n > b_n (l - l/2) <=> a_n > l/2 b_n$ \
    Dunque, se $display(sum^infinity_(k = 1)) b_k$ diverge, grazie alla precedente relazione, per il @srs:cfr $display(sum^infinity_(k = 1)) a_k$ diverge \
    Ora sia $l = +infinity$. Per definizione, $forall M > 0 " " exists nu_M in NN : a_n / b_n > M, forall n > nu_M <=> a_n > M b_n$. Dunque, per il @srs:cfr, se $display(sum^infinity_(k = 1)) b_k$ diverge, anche $display(sum^infinity_(k = 1)) a_k$ diverge
])
#note-box([
  Se $a_n tilde b_n$, allora $l = 1$.
])
#pagebreak()
#outline(title: [Indice dei dimostrabili], target: figure
  .where(kind: "theorem")
  .or(figure.where(kind: "proposition"))
  .or(figure.where(kind: "lemma")))
