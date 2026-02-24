#import "template.typ": *
#import math: *

#show: polypst(
  [Analisi Matematica I],
  [Andrea Giurgola - Prof. Fabio Punzo \ Ingegneria Elettronica, Politecnico di Milano],
  demIndex: true,
)

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
    Sia $q in RR, q != 1$. $display(sum^n_(k = 0)) q^k = (1 - q^(n + 1))/(1 - q), forall n in NN$
  ],
)
#proof([#set par(leading: 1.065em); Sia $p(n)$ la suddetta proposizione. \
  $p(0)$: $q^0 = (1 - q^1)/(1 - q), 1 = cancel(1 - q)/cancel(1 - q), 1 = 1$. Pertanto $p(0)$ è vera. \

  $p(n + 1)$: $display(sum^(n + 1)_(k = 0)) q^k = (1 - q^(n + 2))/(1 - q), display(sum^(n + 1)_(k = 0)) q^k = display(sum^(n)_(k = 0)) q^k + q^(n + 1) = (1 - q^(n + 1))/(1 - q) + q^(n + 1) = (1 - cancel(q^(n + 1)) + cancel(q^(n + 1)) - q^(n + 2))/(1 - q) = (1 - q^(n + 2))/(1 - q)$. \ È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

= I numeri

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ NN := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ ZZ := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ QQ := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$.

== I numeri razionali

Due frazioni $a/b$ e $c/d$ si dicono *equivalenti* se vale la relazione $a d = b c$. \

I numeri razionali possono anche essere rappresentati sotto forma di *allineamento decimale* (per esempio $1/2 = 0,5$). Un numero razionale può essere:
- *finito*: la parte decimale ha un numero limitato di cifre
- *periodico*: la parte decimale si ripete all'infinito con costanza

#note-box(
  [Gli allineamenti decimali con periodo $9$ non provengono da alcuna divisione (ad esempio $0.overline(9) = 1$).],
)

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
#proof(
  [Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ],
)

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
#example(
  [$E = (0; 2] => max E = 2, exists.not min E$, $E = [0; 2) => exists.not max E, min E = 0$],
)
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
#warning-box(
  [Sia $a in RR$. Allora $sqrt(a^2) = abs(a)$ poiché il risultato di una radice di ordine pari è sempre positivo.],
)

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
  func(
    $f(x) = x^n, \ forall n in NN$,
    (4, 4),
    (-1.2, 1.2),
    (
      x => calc.pow(x, 2),
      x => calc.pow(x, 3),
    ),
  ),
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

  inverseFunc(
    $f(x) = arcsin(x)$,
    (3, 3),
    (-2 * calc.pi, 2 * calc.pi),
    (
      calc.sin,
    ),
  ),
  inverseFunc(
    $f(x) = arccos(x)$,
    (3, 3),
    (-2 * calc.pi, 2 * calc.pi),
    (
      calc.cos,
    ),
  ),
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

Se infiniti punti di una successione non appartengono alla striscia $S_(l, epsilon), forall epsilon > 0$, allora la successione non ammette limite finito.
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
    - $+infinity$ o _diverge positivamente_ se $forall M > 0 " " exists nu_M in NN : a_n > M, forall n > nu_M$
    - $-infinity$ o _diverge negativamente_ se $forall M > 0 " " exists nu_M in NN : a_n < -M, forall n > nu_M$
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
  display(lim_(n -> infinity)) (a_n b_n) &= cases(a dot b &"se" a != plus.minus infinity \, b != plus.minus infinity, plus.minus infinity &"se" a > 0 \, b = plus.minus infinity, minus.plus infinity &"se" a < 0 \, b = plus.minus infinity, +infinity &"se" a = b = plus.minus infinity, minus infinity &"se" a = plus.minus infinity \, b = minus.plus infinity) \
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
]) <lms:cprm>
#proof([
  Supponiamo, per assurdo, che $a < 0$. Allora, per il @lms:prm si avrebbe $a_n < 0$ definitivamente, il che è un assurdo.
])
#corollary(
  title: [Proprietà del confronto],
  [
    Se $display(lim_(n -> infinity)) a_n = a, display(lim_(n -> infinity)) b_n = b, a_n >= b_n, forall n in NN$ allora $a >= b$.
  ],
) <lms:pcfr>
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
#lemma(
  title: [Limite del valore assoluto di una successione infinitesima],
  [
    Sia ${a_n}$ una successione. Allora $display(lim_(n -> infinity)) a_n = 0 <=> display(lim_(n -> infinity)) abs(a_n) = 0$
  ],
) <lms:lmp>
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
  $abs(a_n b_n) >= 0 <=> abs(a_n)abs(b_n) >= 0, forall n in NN$. Visto che $display(lim_(n -> infinity)) a_n = M => abs(a_n) <= M <=> abs(a_n)abs(b_n) <= underbrace(M abs(b_n), -> 0)$ \
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
  - $a > 1$: $x = a - 1 => a^n >= 1 + n(a - 1), display(lim_(n -> infinity)) (1 + n(a - 1)) = +infinity$ \ #"          " Per il @lms:pcfr, $display(lim_(n -> infinity)) a_n = +infinity$
  - $a = 1$: $1^n = 1, forall n in NN <=> display(lim_(n -> infinity)) 1^n = 1$
  - $-1 < a < 1$: $abs(a^n) = abs(a)^n = 1/underbrace((1/abs(a))^n, -> +infinity) => display(lim_(n -> infinity)) a^n = 0$
  #set par(leading: 2em)
  - $a = 0$: $0^n = 0, forall n in NN => display(lim_(n -> infinity)) 0^n = 0$
  - $a <= -1$: $cases(display(lim_(k -> infinity)) a^(2k) &= cases(1 &"se" a = -1, +infinity &"se" a < -1), display(lim_(k -> infinity)) a^(2k + 1) &= cases(-1 &"se" a = -1, -infinity &"se" a < -1), reverse: #true) => exists.not display(lim_(n -> infinity)) a_n$
])
- *Radici*
$
  display(lim_(n -> infinity)) root(n, a) = 1, display(lim_(n -> infinity)) root(n, a^b) = 1 "con" b in RR
$
#proof([
  - $a > 1$: Sia $b_n := root(n, a) - 1$, dunque $b_n >= 0, forall n in NN$ \ #"          " Per il @ind:brn, $(1 + b_n)^n >= 1 + b_n n => (root(n, a))^n >= 1 + b_n n$ \ #"          " $<=> a >= 1 + b_n n => 0 <= b_n <= (a - 1)/n$ \ #"          " Per il @lms:tdc, $display(lim_(n -> infinity)) b_n = 0 => display(lim_(n -> infinity)) root(n, a) = 1$
  #set par(leading: 1em)
  - $0 < a < 1$: $root(n, a) = 1 / underbrace(root(n, 1 / a), -> 1) -> 1 / 1 = 1 => display(lim_(n -> infinity)) root(n, a) = 1$
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
      $overline(A B) = 1, accent(B C, paren.t) =: x, overline(C E) = sin x, overline(B D) = tan x$ \
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
            ((calc.cos(calc.pi / 4), calc.sin(calc.pi / 4)), (1, 0)),
            style: (stroke: (paint: red)),
          )
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
  1. $log(1 + a_n)/a_n = 1/a_n log(1 + a_n) = log((1 + a_n)^(1/a_n))$. Sia ora $b_n := 1/a_n$, dunque $display(lim_(n -> infinity)) b_n = 0$. \
  #"   " $<=> display(lim_(n -> infinity)) log(underbrace((1 + 1/b_n)^(b_n), -> e)) = log e = 1$
  2. Sia $c_n := e^(a_n) - 1$, dunque $display(lim_(n -> infinity)) c_n = 0$. Poiché il limite precedente vale per una qualsiasi $a_n$\
  #"   " $log(1 + c_n)/c_n = log(cancel(1) + e^(a_n) - cancel(1))/c_n = (a^n log(e)) / (e^(a_n) - 1) = a^n / (e^(a_n) - 1)$. Dunque $(e^(a_n) - 1)/a_n = 1 / underbrace(a_n / (e^(a_n) - 1), -> 1) => display(lim_(n -> infinity)) (e^(a_n) - 1)/a_n = 1$
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
#theorem(
  title: [Gerarchia degli infiniti],
  [Siano $alpha, a, b in RR, b > 0, alpha > 1$. Allora
    $
      &display(lim_(n -> infinity)) n^b / alpha^n &= 0 &"poiché" alpha^n -> +infinity "prima di" n^b \
      &display(lim_(n -> infinity)) alpha^n / n! &= 0 &"poiché" n! -> +infinity "prima di" alpha^n \
      &display(lim_(n -> infinity)) n! / n^n &= 0 &"poiché" n^n -> +infinity "prima di" n! \
      &display(lim_(n -> infinity)) (log_a (n)) / n^b &= 0 &"poiché" n^b -> +infinity "prima di" log_a (n), "con" a > 0, a != 1, b > 0
    $],
)
#proof([
  1. $b_n := a_(n + 1) / a_n = (n + 1)^b / alpha^(n + 1) dot 1 / (n^b / alpha^n) = (n + 1)^b/(alpha^(n + 1)) dot alpha^n / n^b = underbrace(((n + 1) / n)^b, -> 1) dot 1 / alpha => display(lim_(n -> infinity)) b_n = 1 / alpha = b$. Poiché $b < 1$, allora, per il @lms:crs, $display(lim_(n -> infinity)) a_n = 0$
  2. $b_n := a_(n + 1) / a_n = alpha^(n + 1) / (n + 1)! dot 1 / (alpha^n / n!) = alpha^(n + 1) / (n + 1)! dot n! / alpha^n = alpha dot n! / ((n + 1)n!) = underbrace(alpha / (n + 1), -> 0) => display(lim_(n -> infinity)) b_n = 0 = b$. Poiché $b < 1$, per il @lms:crs, $display(lim_(n -> infinity)) a_n = 0$

  3. $b_n := a_(n + 1) / a_n = (n + 1)! / (n + 1)^n dot n^n / n! = (cancel((n + 1))cancel(n!)) / cancel(n!) dot n^n / ((n + 1)^n cancel((n + 1))) = (n / (n + 1))^n = 1 / ((n + 1) / n)^n = 1 / underbrace((1 + 1 / n)^n, -> e)$ \ $=> display(lim_(n -> infinity)) b_n = 1 / e$. Poiché $b < 1$, per il @lms:crs, $display(lim_(n -> infinity)) a_n = 0$
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
      sin(a_n) tilde a_n & => sin(a_n) = a_n + o(a_n) \
   e^(a_n) - 1 tilde a_n & => e^(a_n) = a_n + o(a_n) \
  log(1 + a_n) tilde a_n & => log(1 + a_n) = a_n + o(a_n) \
         "e così via..." \
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
  alpha = 1, a_k = 1/k^alpha => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) 1/k^alpha = 1 + 1/2^alpha + 1/3^alpha + 1/4^alpha + ...
$
- *Serie geometrica*: il suo risultato dipende da una certa $x in RR$ detta *ragione*
$
  a_k = x^k, x != 1 => s_n = display(sum^n_(k = 1)) a_k = display(sum^n_(k = 1)) x^k = x + x^2 + x^3 + x^4 + ... = (1 - x^(n + 1)) / (1 - x) \
  => display(lim_(n -> infinity)) s_n = cases(exists.not &"se" x <= -1, 1 / (1 - x) &"se" -1 < x < 1, +infinity &"se" x >= 1)
$

#theorem(
  title: [Condizione necessaria per la convergenza di una serie],
  [
    $display(sum^infinity_(k = 1)) a_k$ convergente $=> display(lim_(n -> infinity)) a_n = 0$
  ],
)
#proof([
  Sia $display(lim_(n -> infinity)) s_n =: s$, con $s in RR$ poiché ${s_n}$ convergente per ipotesi. \
  $s_n = s_(n - 1) + a_n <=> a_n = s_n - s_(n - 1)$. In questo caso $display(lim_(n -> infinity)) s_n = s$ e $display(lim_(n -> infinity)) s_(n - 1) = s$. \
  $=> display(lim_(n -> infinity)) a_n = display(lim_(n -> infinity)) (s_(n - 1) - s_n) = s - s = 0$.
])
#warning-box([
  $display(lim_(n -> infinity)) a_n = 0 arrow.r.double.not display(sum^infinity_(k = 1)) a_k$ convergente.
])

#proposition(
  title: [Proprietà di una serie],
  [
    - Se $display(sum^infinity_(k = 1)) a_k$ e $display(sum^infinity_(k = 1)) b_k$ sono regolari e la somma $display(sum^infinity_(k = 1)) a_k + display(sum^infinity_(k = 1)) b_k$ ha significato, allora \ $display(sum^infinity_(k = 1)) (a_k + b_k) = display(sum^infinity_(k = 1)) a_k + display(sum^infinity_(k = 1)) b_k$.
    - Se $display(sum^infinity_(k = 1)) a_k$ è regolare, allora $display(sum^infinity_(k = 1)) c a_k = c display(sum^infinity_(k = 1)) a_k, forall c in RR$.
  ],
)
#theorem(
  title: [Carattere di una serie a termini non negativi],
  [
    Una serie $display(sum^infinity_(k = 1)) a_k$ con $a_k >= 0, forall k in NN$ è convergente o divergente positivamente.
  ],
)
#proof([
  Sia $s_n := display(sum^n_(k = 1)) a_k$. Dunque $s_n = a_1 + a_2 + ... + a_n$ e $s_(n + 1) = a_1 + ... + a_n + a_(n + 1)$ \
  $=> s_(n + 1) >= s_n$. Poiché $a_k >= 0, forall k in NN => s_n$ crescente. \
  Per il @lms:reg, $exists display(lim_(n -> infinity)) s_n$, il quale può essere un certo $l in RR$ oppure $+infinity$.
])

== Criteri di convergenza

#theorem(
  title: [Criterio del confronto di serie],
  [
    #set list(spacing: 1em)
    Siano ${a_n}, {b_n}$ due successioni tali che $0 <= a_n <= b_n, forall n in NN$. Allora:
    - $display(sum^infinity_(k = 1)) b_k$ convergente $=> display(sum^infinity_(k = 1)) a_k$ convergente
    - $display(sum^infinity_(k = 1)) a_k$ divergente $=> display(sum^infinity_(k = 1)) b_k$ divergente
  ],
) <srs:cfr>
#proof([
  Siano $s_n := display(sum^infinity_(k = 1)) a_k, t_n := display(sum^infinity_(k = 1)) b_k$. $a_k <= b_k, forall k in NN => s_n <= t_n, forall n in NN$. \
  Poiché $a_k >= 0, b_k >= 0, forall k in NN => s_n, t_n$ crescenti. \
  Per il @lms:reg $exists display(lim_(n -> infinity)) s_n = s, display(lim_(n -> infinity)) t_n = t$. Dunque:
  - $t_n$ convergente $=> t in RR$. Per il @lms:pcfr, $s_n <= t_n => s <= t => s in RR => s_n$ convergente
  - $s_n$ divergente $=> s = +infinity$. Per il @lms:pcfr, $s_n <= t_n => s <= t => t = +infinity => t_n$ divergente
])
#theorem(
  title: [Criterio del confronto asintotico],
  [
    #set list(spacing: 1em)
    Siano ${a_n}, {b_n}$ due successioni tali che $a_n >= 0, b_n > 0, forall n in NN$ e $display(lim_(n -> infinity)) a_n / b_n = l$, con $l in [0; + infinity]$:
    - $display(sum^infinity_(k = 1)) b_k$ convergente e $l in [0; +infinity) => display(sum^infinity_(k = 1)) a_k$ convergente
    - $display(sum^infinity_(k = 1)) b_k$ divergente e $l in (0; +infinity] => display(sum^infinity_(k = 1)) a_k$ divergente
  ],
)
#proof([
  Per definizione, $display(lim_(n -> infinity)) a_n / b_n <=> forall epsilon > 0 " " exists nu_epsilon in NN : abs(a_n / b_n - l) < epsilon, forall n > nu_epsilon$ \
  $<=> l - epsilon < a_n / b_n < l + epsilon, forall n > nu_epsilon$. Poiché $b_n > 0 => b_n (l - epsilon) < a_n < b_n (l + epsilon), forall n > nu_epsilon$.
  - Se $display(sum^infinity_(k = 1)) b_k$ converge, allora, grazie a $a_n < b_n (l + epsilon)$, per il @srs:cfr $display(sum^infinity_(k = 1)) a_k$ converge
  - Sia $l in (0; +infinity)$. Scegliamo $epsilon = l/2 => a_n > b_n (l - l/2) <=> a_n > l/2 b_n$ \
    Dunque, se $display(sum^infinity_(k = 1)) b_k$ diverge, grazie alla precedente relazione, per il @srs:cfr $display(sum^infinity_(k = 1)) a_k$ diverge \
    Ora sia $l = +infinity$. Per definizione, $forall M > 0 " " exists nu_M in NN : a_n / b_n > M, forall n > nu_M <=> a_n > M b_n$. Dunque, per il @srs:cfr, se $display(sum^infinity_(k = 1)) b_k$ diverge, anche $display(sum^infinity_(k = 1)) a_k$ diverge
])
#note-box([
  Se $a_n tilde b_n$, allora $l = 1$, quindi le serie $display(sum^infinity_(k = 1)) a_k$ e $display(sum^infinity_(k = 1)) b_k$ hanno lo stesso carattere.
])
#theorem(
  title: [Criterio del rapporto],
  [
    Sia ${a_n}$ una successione tale che $a_n > 0, forall n in NN$ e $display(lim_(n -> infinity)) a_(n + 1) / a_n = l$ con $l in RR$. Allora
    - $l < 1 => display(sum^infinity_(k = 1)) a_k$ convergente
    - $l > 1 => display(sum^infinity_(k = 1)) a_k$ divergente
  ],
)
#proof([
  - Sia $x$ tale che $l < x < 1$ e $epsilon = x - l$, dunque $epsilon > 0$. \
    $exists nu in NN : 0 < a_(n + 1) / a_n < x, forall n > nu$. Poiché $l + epsilon = x$, si può dire $0 < a_(n + 1) / a_n < l + epsilon$. \
    Supponiamo che $nu = 1$. Allora si ha che:
    - $n = 1 => a_2 / a_1 < x <=> a_2 < a_1 x$
    - $n = 2 => a_3 / a_2 < x <=> a_3 < a_2 x <=> a_3 < a_2 x < a_1 x^2$
    $=> a_n < a_1 x^(n - 1)$. Sia ora $b_n := a_1 x^(n - 1)$. Dunque \
    $display(sum^infinity_(k = 1)) b_k = display(sum^infinity_(k = 1)) a_1 x^(k - 1) = a_1 display(sum^infinity_(k = 1)) x^(k - 1)$. Stabiliamo $s = k - 1$, quindi $display(sum^infinity_(s = 0)) x^s$. Questa è una serie geometrica, ed, essendo $0 < x < 1$, sappiamo che converge. Quindi anche $display(sum^infinity_(k = 1)) b_k$ converge. \
    Per il @srs:cfr, anche $display(sum^infinity_(k = 1)) a_k$ converge.
  - Per definizione, $forall epsilon > 0 " " exists nu_epsilon in NN : abs(a_(n + 1) / a_n - l) < epsilon, forall n > nu_epsilon <=> l - epsilon < a_(n + 1) / a_n < l + epsilon$. \
    Scegliamo $epsilon = l - 1$, quindi $epsilon > 0$ e $l - epsilon = 1$. Dunque $a_(n + 1) / a_n > 1, forall n > nu_epsilon <=> a_(n + 1) > a_n$ \
    $=> {a_n}$ definitivamente crescente. Poiché ${a_n}$ è crescente e positiva, non può essere infinitesima \
    #set par(leading: 1.2em)
    $=> display(sum^infinity_(k = 1)) a_k$ divergente
])
#theorem(
  title: [Criterio della radice],
  [
    Sia ${a_n}$ una successione tale che $a_n >= 0, forall n in NN$ e $display(lim_( -> infinity)) root(n, a_n) = l$ con $l in RR$. Allora:
    - $l < 1 => display(sum^infinity_(k = 1)) a_k$ convergente
    - $l > 1 => display(sum^infinity_(k = 1)) a_k$ divergente
  ],
)
#theorem(
  title: [Criterio di Leibnitz],
  [
    Sia ${a_n}$ una successione tale che $a_n > 0, display(lim_(n -> infinity)) a_n = 0$ e ${a_n}$ decrescente. Allora $display(sum^infinity_(k = 1)) (-1)^k a_k$ converge. Inoltre $abs(s_n - s) <= a_(n + 1)$, dove $s_n$ è la somma parziale della suddetta serie e $display(lim_(n -> infinity)) s_n = s$.
  ],
)

== Convergenza assoluta

#definition(
  title: [Convergenza assoluta],
  [
    Sia ${a_n}$ una successione. Allora $display(sum^infinity_(k = 1)) a_k$ _converge assolutamente_ se anche $display(sum^infinity_(k = 1)) abs(a_k)$ converge.
  ],
)
#theorem(title: [Carattere di una serie assolutamente convergente], [
  Una serie assolutamente convergente è anche convergente.
])
#warning-box([
  La convergenza non implica la convergenza assoluta.
])

= Limiti di funzioni



#definition(
  title: [Limiti di funzioni all'infinito],
  [
    Siano $f: A -> RR$ con $(a, +infinity) subset.eq A subset.eq RR, l in RR$. Allora:
    - $forall epsilon > 0 " " exists nu_epsilon > 0 : abs(f(x) - l) < epsilon, forall x > nu_epsilon, x in A => display(lim_(x -> +infinity)) f(x) = l$
    - $forall M > 0 " " exists nu_M > 0 : f(x) > M, forall x > nu_M, x in A => display(lim_(x -> +infinity)) f(x) = +infinity$
    - $forall M > 0 " " exists nu_M > 0 : f(x) < -M, forall x > nu_M, x in A => display(lim_(x -> +infinity)) f(x) = -infinity$
    - $forall epsilon > 0 " " exists nu_epsilon > 0 : abs(f(x) - l) < epsilon, forall x < nu_epsilon, x in A => display(lim_(x -> -infinity)) f(x) = l$
    - $forall M > 0 " " exists nu_M > 0 : f(x) > M, forall x < nu_M, x in A => display(lim_(x -> -infinity)) f(x) = +infinity$
    - $forall M > 0 " " exists nu_M > 0 : f(x) < -M, forall x < nu_M, x in A => display(lim_(x -> -infinity)) f(x) = -infinity$
  ],
)
#definition(
  title: [Intorno],
  [
    Siano $r > 0, x_0 in RR$. Si dice _intorno circolare_ di centro $x_0$ e raggio $r$ l'insieme $I_r (x_0) := {x in RR : abs(x - x_0) < r}$. Si dice _intorno destro_ l'insieme $I_r^+ (x_0) := {x in RR : x_0 < x < x_0 + r}$ e si dice _intorno sinistro_ l'insieme $I_r^- (x_0) := {x in RR : x_0 - r < x < x_0}$.
  ],
)
#definition(
  title: [Punto di accumulazione],
  [
    Siano $E subset.eq RR, x_0 in RR$. $x_0$ si dice _punto di accumulazione_ di $E$ se $forall r > 0 " " [I_r (x_0) inter E] \\ {x_0} != emptyset$. $x_0$ si dice _punto di accumulazione destro_ se $forall r > 0 " " [I_r^+ (x_0) inter E] \\ {x_0} = emptyset$ e si dice _punto di accumulazione sinistro_ se $forall r > 0 " " [I_r^- (x_0) inter E] \\ {x_0} != emptyset$.
  ],
)

#definition(
  title: [Limiti di funzioni al finito],
  [
    Siano $f: A -> RR, A subset.eq RR, x_0$ punto di accumulazione per $A$. Allora:
    - $forall epsilon > 0 " " exists delta_(epsilon, x_0) > 0 : abs(f(x) - l) < epsilon, forall x in I_(delta_(epsilon, x_0)) (x_0) inter A, x != x_0 => display(lim_(x -> x_0)) f(x) = l$
    - $forall M > 0 " " exists delta_(M, x_0) > 0 : f(x) > M, forall x in I_(delta_(M, x_0)) (x_0) inter A, x != x_0 => display(lim_(x -> x_0)) f(x) = +infinity$
    - $forall M > 0 " " exists delta_(M, x_0) > 0 : f(x) < -M, forall x in I_(delta_(M, x_0)) (x_0) inter A, x != x_0 => display(lim_(x -> x_0)) f(x) = -infinity$

    Per $x_0^+$ e $x_0^-$ si considerano nell'espressione gli intorni $I_delta^+ (x_0)$ e $I_delta^- (x_0)$.
  ],
)
#note-box([
  $display(lim_(x -> x_0^-)) f(x) = display(lim_(x -> x_0^+)) f(x) => display(lim_(x -> x_0)) f(x) = l$ con $l in RR$ \
  $display(lim_(x -> x_0^-)) f(x) != display(lim_(x -> x_0^+)) f(x) => exists.not display(lim_(x -> x_0)) f(x)$ \
  $x_0$ punto di accumulazione sia destro che sinistro e $display(lim_(x -> x_0)) f(x) = l => display(lim_(x -> x_0^-)) f(x) = display(lim_(x -> x_0^+)) f(x) = l$
])

#theorem(
  title: [Teorema ponte],
  [
    Siano $A subset.eq RR, {x_n}$ una successione con ${x_n} subset.eq A, f: A -> RR, A subset.eq RR, l in RR, x_0$ punto di accumulazione per $A$. Allora $display(lim_(x -> x_0)) f(x) = l <=> forall {x_n} in A \\ {x_0}, display(lim_(n -> infinity)) x_n, display(lim_(n -> +infinity)) f(x_n) = l$.
  ],
) <lmf:pnt>
#note-box([
  Se ${x_n}, {y_n} subset A \\ {x_0}, display(lim_(n -> infinity)) x_n = display(lim_(n -> infinity)) y_n = x_0, display(lim_(n -> infinity)) f(x_n) != display(lim_(n -> infinity)) f(y_n)$ allora $exists.not display(lim_(x -> infinity)) f(x)$
])

#theorem(title: [Unicità del limite], [
  Sia $f$ una funzione. Se $f$ ammette limite, esso è unico.
])

#theorem(
  title: [Permanenza del segno],
  [
    Siano $A subset.eq RR, f: A -> RR, x_0$ punto di accumulazione per $A$. Se $display(lim_(x -> x_0)) f(x) = M$ con $M > 0$ allora $exists delta > 0 " " f(x) > M / 2, forall x in A inter I_delta (x_0), x != x_0$, quindi $f(x) > 0$.
  ],
) <lmf:prm>
#theorem(
  title: [Teorema dei due carabinieri],
  [
    Siano $A subset.eq RR, f, g, h$ tre funzioni con $g(x) <= f(x) <= h(x), forall x in [I_sigma (x_0) \\ {x_0}] inter A$ per qualche $sigma > 0$ e $display(lim_(x -> x_0)) g(x) = display(lim_(x -> x_0)) h(x) = l$ con $l in RR$. Allora $display(lim_(x -> x_0)) f(x) = l$.
  ],
) <lmf:tdc>
#lemma(
  title: [Limite del valore assoluto di una funzione infinitesima],
  [
    $display(lim_(x -> infinity)) f(x) = 0 <=> display(lim_(x -> infinity)) abs(f(x))$
  ],
)
#corollary(
  title: [Limite del prodotto di funzioni],
  [
    Se $display(lim_(x -> x_0)) f(x) = 0$ e $g$ limitata in $I_delta (x_0)$ allora $display(lim_(x -> x_0)) f(x)g(x) = 0$.
  ],
)

#theorem(
  title: [Limite di funzioni monotone],
  [
    Siano $f$ una funzione e $x_0 in (a, b)$. Allora: \
    $
      lim_(x -> x_0^-) f(x) = cases(display(sup_(a < x < x_0)) f(x) &"se" f arrow.tr "in" (a,b), display(inf_(a < x < x_0)) f(x) &"se" f arrow.br "in" (a, b)), lim_(x -> x_0^+) f(x) = cases(display(inf_(x_0 < x < b)) f(x) &"se" f arrow.tr "in" (a, b), display(sup_(x_0 < x < b)) f(x) &"se" f arrow.br "in" (a, b))
    $
    $
      lim_(x -> +infinity) f(x) = cases(display(sup_(x > a)) f(x) &"se" f arrow.tr "in" (a, +infinity), display(inf_(x > a)) f(x) &"se" f arrow.br "in" (a, +infinity)), lim_(x -> -infinity) f(x) = cases(display(sup_(x < a)) f(x) &"se" f arrow.tr "in" (-infinity, a), display(inf_(x < a)) f(x) &"se" f arrow.br "in" (-infinity, a))
    $
  ],
)

== Limiti notevoli

- *Goniometrici*: $display(lim_(x -> 0)) sin x = 0, display(lim_(x -> 0)) f(x) cos x = 1, display(lim_(x -> 0)) (sin x) / x = 1, display(lim_(x -> 0)) (1 - cos x) / x^2 = 1 / 2$

- *Esponenziali*: $display(lim_(x -> +infinity)) (1 + 1 / x)^x = e, display(lim_(x -> +infinity)) log(1 + x) / x = 1, display(lim_(x -> +infinity)) (e^x - 1) / x = 1, display(lim_(x -> +infinity)) ((1 + x)^alpha - 1) / x = alpha$

- *Gerarchia degli infiniti*: $display(lim_(x -> +infinity)) (log_a (x)) / x^alpha = 0, display(lim_(x -> +infinity)) x^alpha / a^x = 0$

#pagebreak()

== Infiniti, infinitesimi e asintoti
#definition(
  title: [Funzione infinitesima],
  [
    Una funzione $f$ si dice _infinitesima per $x -> x_0$_ se $display(lim_(x -> x_0)) f(x) = 0$. Analogamente per $x -> plus.minus infinity$.
  ],
)
#definition(
  title: [Funzione infinita],
  [
    Una funzione $f$ si dice _infinita per $x -> x_0$_ se $display(lim_(x -> x_0)) f(x) = +plus.minus infinity$. Analogamente per $x -> plus.minus infinity$.
  ],
)
#definition(
  title: [Ordini di infinitesimi],
  [
    Siano $f, g$ due funzioni infinitesime per $x -> x_0$. Allora:
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = 0$, $f$ è un _infinitesimo di ordine superiore_ rispetto a $g$
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = l$ con $l in RR$, $f$ e $g$ sono _infinitesimi dello stesso ordine_
    - Se $display(lim_(x -> x_0)) f(x) = g(x) = plus.minus infinity$, $f$ è un _infinitesimo di ordine inferiore_ rispetto a _g_
    - Se $exists.not display(lim_(x -> x_0)) f(x) / g(x)$, $f$ e $g$ sono _non paragonabili_
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = 1$, $f$ e $g$ sono _asintoticamente equivalenti_
    Analogamente per $x -> plus.minus infinity$.
  ],
)
#definition(
  title: [Ordini di infiniti],
  [
    Siano $f, g$ due funzioni infinite per $x -> x_0$. Allora:
    - Se $display(lim_(x -> x_0)) f(x) = g(x) = plus.minus infinity$, $f$ è un _infinito di ordine inferiore_ rispetto a _g_
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = 0$, $f$ è un _infinito di ordine superiore_ rispetto a $g$
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = l$ con $l in RR$, $f$ e $g$ sono _infiniti dello stesso ordine_
    - Se $exists.not display(lim_(x -> x_0)) f(x) / g(x)$, $f$ e $g$ sono _non paragonabili_
    - Se $display(lim_(x -> x_0)) f(x) / g(x) = 1$, $f$ e $g$ sono _asintoticamente equivalenti_
    Analogamente per $x -> plus.minus infinity$.
  ],
)
#definition(
  title: [O-piccolo],
  [
    Siano $f, g$ due funzioni. Se $display(lim_(x -> x_0)) f(x) / g(x) = 0$ allora $f(x) = o(g(x))$ per $x -> x_0$. Analogamente per $x -> +infinity$ e $x -> -infinity$.
  ],
)

Se $display(lim_(x -> x_0)) f(x) = plus.minus infinity$ o $display(lim_(x -> x_0^+)) f(x) = plus.minus infinity, display(lim_(x -> x_0^-)) f(x) = minus.plus infinity$, allora la retta $x = x_0$ è un *asintoto verticale* di $f$, mentre se il limite va a infinito solo per $x -> x_0^+$ o solo per $x -> x_0^-$ allora la retta $x = x_0$ si dice l'*asintoto destro* o *sinistro* di $f$. \
Se $display(lim_(x -> plus.minus infinity)) f(x) = b$ con $b in RR$, la retta $y = b$ si dice *asintoto orizzontale* di $f$.

#definition(
  title: [Asintoto],
  [
    Sia $f: C -> RR$ con $C = (c, +infinity)$. La retta $y = m x + q$ si dice _asintoto_ di $f$ per $x -> +infinity$ se $display(lim_(x -> +infinity)) (f(x) - m x - q) = 0$. Lo stesso vale con $C = (-infinity, c)$ e $x -> -infinity$.
  ],
)
Dunque, se $m = 0$ si ha un asintoto orizzontale, viceversa si ha un *asintoto obliquo*.

Poiché $display(lim_(x -> +infinity)) (f(x) - m x - q) / x = 0$ e $display(lim_(x -> +infinity)) q / x = 0$ allora $m = display(lim_(x -> +infinity)) f(x) / x$ e $q = display(lim_(x -> +infinity)) (f(x) - m x)$.

== Continuità

#definition(
  title: [Funzione continua],
  [
    Siano $f: A -> RR$ con $A subset.eq RR$, $x_0 in A$ punto di accumulazione per $A$. Allora $f$ si dice _continua in $x_0$_ se $display(lim_(x -> x_0)) f(x) = f(x_0)$. Se $f$ è continua $forall x_0 in A$ allora si dice _continua in $A$_.
  ],
)
#note-box([
  Secondo la definizione di limite, $forall epsilon > 0 " " exists delta_(epsilon, x_0) > 0 : abs(f(x) - f(x_0)) < epsilon, forall x in (A inter I_delta_(epsilon, x_0) (x_0))$.
])
#proposition(
  title: [Continuità delle funzioni goniometriche],
  [
    $display(lim_(x -> x_0)) sin x = sin x_0, display(lim_(x -> x_0)) cos x = cos x_0$
  ],
) <lmf:cgn>
#proof([
  Ricordiamo che $sin a - sin b = -2sin((a - b) / 2)cos((a + b) / 2)$ e $cos x - cos b = 2sin((a - b) / 2)cos((a + b) / 2)$ per le formule di prostaferesi. Allora \
  $abs(sin x - sin x_0) = 2abs(sin((x - x_0) / 2)cos((x + x_0) / 2))$. Poiché $abs(sin a) <= abs(a)$ e $abs(cos(a)) <= 1$ ,allora \
  $0 <= abs(sin x - sin x_0) <= 2 abs((x - x_0) / 2) dot 1 <=> abs(sin x - sin x_0) <= underbrace(abs(x - x_0), -> 0)$. Quindi, per il @lmf:tdc, $display(lim_(x -> x_0)) abs(sin x - sin x_0) = 0 <=> display(lim_(x -> x_0)) sin x = sin x_0$. Allo stesso modo, si ha anche $0 <= abs(cos x - cos x_0) <= abs(x - x_0)$. Quindi, per il @lmf:tdc, $display(lim_(x -> x_0)) abs(cos x - cos x_0) = 0 <=> display(lim_(x -> x_0)) cos x = cos x_0$.
])
#note-box([
  $display(lim_(x -> x_0)) tan x = display(lim_(x -> x_0)) (sin x) / (cos x) = (sin x_0) / (cos x_0) = tan x_0, display(lim_(x -> x_0)) cot x = display(lim_(x -> x_0)) (cos x) / (sin x) = (cos x_0) / (sin x_0) = cot x_0$
])

In generale, per l'algebra dei limiti, si dimostra che un qualsiasi polinomio $p(x), sin x, cos x, tan x$, $cot x, a^x, sinh x, cosh x$ sono tutte continue nel loro dominio.

#theorem(
  title: [Limite della funzione composta],
  [
    Siano $f(x)$ una funzione con $display(lim_(x -> x_0)) f(x) = y_0$ e $g(y)$ una funzione continua in $y_0$. Allora

    $display(lim_(x -> x_0)) g(f(x)) = g(display(lim_(x -> x_0)) f(x)) = g(y_0)$.
  ],
) <lmf:lfc>
#corollary(
  title: [Continuità della funzione composta],
  [
    Siano $f(x)$ una funzione continua in $x_0$ e $g(y)$ una funzione continua in $y_0$ con $y_0 = f(x_0)$. Allora la funzione $g(f(x))$ è continua in $x_0$.
  ],
)
#proof([
  $f(x)$ è continua in $x_0$ per ipotesi, quindi $display(lim_(x -> x_0)) f(x) = f(x_0) = y_0$. Per il @lmf:lfc, $display(lim_(x -> x_0)) g(f(x)) = g(display(lim_(x -> x_0)) f(x)) = g(f(x_0)) = g(y_0)$. Quindi $g(f(x))$ è continua in $x_0$.
]) \ \

Grazie al @lmf:pnt, abbiamo il seguente teorema.
#theorem(
  title: [Continuità per successione],
  [
    Una funzione $f: A -> RR$ con $A subset.eq RR$ è continua in $x_0 in A$ se e solo se $display(lim_(n -> infinity)) f(x_n) = f(x_0)$, $forall {x_n} subset.eq A$ con $display(lim_(n -> infinity)) x_n = x_0$.
  ],
)
=== Continuità della funzione inversa

#theorem(
  title: [Continuità della funzione inversa],
  [
    Sia $f$ una funzione definita in un intervallo $I$, continua ed invertibile. Allora $f^(-1)$ è continua.
  ],
) <lmf:cnv>
#warning-box(
  [Il @lmf:cnv è falso se $I$ non è un intervallo, quindi, ad esempio, se $I = [1, 2] union [3, 4]$],
)
Grazie al @lmf:cnv, si ha anche che $log_a x$ è continua se $a > 0, a != 1$.
#theorem(title: [Continuità delle funzioni goniometriche e le loro inverse], [
  Le funzioni circolari e le loro inverse sono continue.
])
#proof([
  Sappiamo che $sin x, cos x, tan x, cot x$ sono continue per la @lmf:cgn. Dalla stessa si ha anche che $arcsin x, arccos x, arctan x, "arccot"x$ sono continue.
])

=== Punti di discontinuità

#definition(
  title: [Punto di discontinuità],
  [
    Siano $f: A -> RR$ con $A subset.eq RR$ e $x_0 in A$ punto di accumulazione per $A$. Se $f$ non è continua in $x_0$, allora $x_0$ si dice _punto di discontinuità_ di $f$.
  ],
)

Si possono avere punti di discontinuità in diversi casi:
- $display(lim_(x -> x_0^-)) f(x) != display(lim_(x -> x_0^+)) f(x) => x_0$ si dice *punto di discontinuità di 1ª specie* o *salto*. Per esempio, $f(x) = [x]$ presenta un salto in ogni $x$ intera.

- $display(lim_(x -> x_0^-)) f(x) = plus.minus infinity$ o $display(lim_(x -> x_0^+)) f(x) = plus.minus infinity => x_0$ si dice *punto di discontinuità di 2ª specie*. Per esempio, $f(x) = 1 / x$ presenta questa specie di discontinuità in $x = 0$.

- $exists.not display(lim_(x -> x_0^-)) f(x)$ o $exists.not display(lim_(x -> x_0^+)) f(x) => x_0$ si dice *punto di discontinuità di 3ª specie*. Per esempio la funzione $f(x) = cases(sin 1/x &"se" x != 0, 1 &"se" x = 0)$ presenta una discontinuità di 3ª specie in $x = 0$.

- $display(lim_(x -> x_0^-)) f(x) = display(lim_(x -> x_0^+)) f(x) = l$ e $f(x_0) != l$ o $x_0 in.not A => x_0$ si dice *punto di discontinuità eliminabile*. Infatti si può ridefinire la medesima funzione come $hat(f)(x) = cases(f(x) &"se" x != x_0, l &"se" x = x_0)$ dove $hat(f)$ è detta *estensione continua* di $f$.

=== Teoremi sulla continuità

#theorem(
  title: [Permanenza del segno per funzioni continue],
  [
    Siano $f$ una funzione continua in $A subset.eq RR$ e $x_0 in A$. Se $f(x_0) gt.lt c$ con $c in RR$, allora \
    $exists I_x_0 : f(x) gt.lt c, forall x in I_x_0 inter A$.
  ],
) <lmf:prmc>
#proof([
  Per il @lmf:prm, poiché $f$ è continua in $x_0$, $display(lim_(x -> x_0)) (f(x) - c)= f(x_0) - c$, il che è $gt.lt 0$, quindi $f(x_0) gt.lt c$.
])

#theorem(
  title: [Esistenza degli zeri],
  [
    Sia $f$ una funzione continua nell'intervallo $I = [a, b]$. Se $f(a)$ e $f(b)$ hanno segno discorde, allora $exists x_0 in (a, b) : f(x_0) = 0$, dove $x_0$ è detto _zero di $f(x)$_.
  ],
) <lmf:esz>
#proof([
  Sia $c = (a + b) / 2$. Se $f(c) = 0$ allora $x_0 = c$. Se $f(c) > 0$ allora la funzione assume valori discordi in $a$ e $c$, mentre, se $f(c) < 0$, allora assume valori discordi in $b$ e $c$. \
  Consideriamo ora l'intervallo $[a_1, b_1]$, dove $a_1 = cases(a &"se" f(c) > 0, c &"se" f(c) < 0)$ e $b_1 = cases(c &"se" f(c) > 0, b &"se" f(c) < 0)$. In questo modo, abbiamo che $f(a_1)$ e $f(b_1)$ hanno segni discordi. Sia ora $c_1 = (a_1 + b_1) / 2$ e ripetiamo il ragionamento. \
  Otterremo dunque tre successioni, ossia ${a_n}, {b_n}, {c_n}$, dove $c_n = (a_n + b_n) / 2$ e, se $f(c_n) > 0$, abbiamo che $a_(n + 1) = a_n$ e $b_(n + 1) = b_n$, mentre, se $f(c_n) < 0$, abbiamo che $a_(n + 1) = c_n$ e $b_(n + 1) = b_n$. \
  Possiamo iterare questo processo finché $f(c_n) = 0$, ossia quando avremo trovato lo zero della funzione in $(a, b)$. \
  ${a_n}$ è crescente e ${b_n}$ è decrescente. Inoltre $a <= a_n <= c_n <= b_n <= b, forall n >= 1$. Di conseguenza, $a_n$ è limitata, quindi per il @lms:reg, esiste $display(lim_(n -> infinity)) a_n = epsilon$. Per il @lms:pcfr, $a <= epsilon <= b$. Notiamo che $b_n - a_n = (b - a) / 2^n <=> b_n = underbrace((b - a) / 2^n, -> 0) + a_n$, quindi $display(lim_(n -> infinity)) b_n = epsilon$. Poiché $f$ è continua in $[a, b]$ per ipotesi:
  - $display(lim_(n -> infinity)) f(a_n) = f(epsilon)$. Poiché $f(a_n) < 0$, per il @lms:cprm, $f(epsilon) <= 0$
  - $display(lim_(n -> infinity)) f(b_n) = f(epsilon)$. Poiché $f(b_n) > 0$, per il @lms:cprm, $f(epsilon) >= 0$
  Dunque, poiché $0 <= f(epsilon) <= 0$, allora $f(epsilon) = 0 <=> x_0 = epsilon$.
])
#note-box([
  Se $f$ è strettamente monotona, lo zero è unico. Inoltre non è necessario che $I$ sia limitato affinché si possa applicare il teorema.
])

#theorem(
  title: [Teorema dei valori intermedi],
  [
    Sia $f$ una funzione continua in un intervallo $I$. Allora $f$ assume tutti i valori compresi tra $display(inf_I) f$ e $display(sup_I) f$. Ossia $forall y_0 in (display(inf_I) f; display(sup_I) f) " " exists x_0 in I : y_0 = f(x_0)$.
  ],
) <lmf:vim>
#proof([
  Siano $m := display(inf_I) f, M := display(sup_I) f$ e $y_0 in (m, M)$. Per definizione, $y_0 > m display(<=>^"def.") exists a in I : f(a) < y_0$ e $y_0 < M display(<=>^"def.") exists b in I : f(b) > y_0$. \
  Sia $g(x) := f(x) - y_0$ con $x in [a,b] subset.eq I$. Dunque $g$ è continua in $[a,b]$. Inoltre $g(a) < 0$ e $g(b) > 0$. Per il @lmf:esz, $exists x_0 in (a, b) : g(x_0) = 0 <=> f(x_0) = y_0$.
])

#definition(
  title: [Massimo e minimo assoluto],
  [
    Siano $f: A -> RR$ con $A subset.eq RR$ e $x_0 in A$. $x_0$ si dice _punto di massimo assoluto_ di $f$ se $f(x) <= f(x_0)$, $forall x in A$. Viceversa, $x_0$ si dice _punto di minimo assoluto_ di $f$ se $f(x) >= f(x_0), forall x in A$.
  ],
)
#theorem(
  title: [Teorema di Weierstrass],
  [
    Una funzione $f: [a, b] -> RR$ continua in $[a, b]$ ammette massimo e minimo assoluti.
  ],
) <lmf:wst>

#warning-box([
  Per tutti questi teoremi è fondamentale sia che la funzione sia continua e che si stia considerando un intervallo, altrimenti nessuno di questi teoremi è applicabile: in particolare per i teoremi di Weierstrass e di esistenza degli zeri, è fondamentale che l'intervallo sia chiuso e limitato.
])

= Derivate

#definition(
  title: [Funzione derivabile e derivata],
  [
    Siano $f: (a, b) -> RR$ e $x_0 in (a, b)$. $f$ si dice _derivabile_ in $x_0$ se $exists display(lim_(h -> 0)) (f(x + h) - f(x)) / h := f'(x_0) in RR$, dove $f'(x_0)$si dice la _derivata di $f$ in $x_0$_. Si può anche indicare $D f(x_0)$ o $lr((dif f(x)) / (dif x)|)_(x = x_0)$.
  ],
)

#grid(
  columns: 2,
  [
    La derivata ha un significato geometrico molto importante: infatti la derivata calcolata in $x = x_0$ rappresenta il *coefficiente angolare* della retta tangente al grafico di $f(x)$ in $x = x_0$. \
    Sappiamo infatti che la retta passante per $P$ e $Q$ ha equazione
    $ r: y = f(x_0) + (f(x_1) - f(x_0)) / (x_1 - x_0) (x - x_0) $
    Se prendiamo un $x_1$ sempre più vicino ad $x_0$, la retta tende a passare da secante a tangente alla curva di $f(x)$. Quindi se consideriamo
  ],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3.5, 3.5),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -2,
      y-max: 11,
      x-min: -2,
      x-max: 11,
      {
        plot.add(domain: (0.1, 11), x => 8 * calc.log(x))
        plot.annotate({
          mark(
            (3, 8 * calc.log(3)),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
            scale: 3.5,
          )
          content((2, 8 * calc.log(3) + 1), "P")
        })
        plot.annotate({
          mark(
            (9, 8 * calc.log(9)),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
            scale: 3.5,
          )
          content((7, 8 * calc.log(9) + 1.5), "Q")
        })
        plot.add-hline(8 * calc.log(3), min: 0, max: 3, style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-hline(8 * calc.log(9), min: 0, max: 9, style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-vline(3, min: 0, max: 8 * calc.log(3), style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-vline(9, min: 0, max: 8 * calc.log(9), style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add(
          domain: (-1, 11),
          x => (4 / 3) * calc.log(3) * (x - 3) + 8 * calc.log(3),
          style: (stroke: (dash: "dashed", paint: yellow)),
        )
        plot.add(
          domain: (-1, 11),
          x => (3.25 / 3) * (x - 3) + 8 * calc.log(3),
          style: (stroke: (dash: "dashed", paint: green)),
        )
        plot.annotate({
          content((-2.25, 8 * calc.log(9)), $f(x_1)$)
          content((-2.25, 8 * calc.log(3)), $f(x_0)$)
          content((3, -1), $x_0$)
          content((9, -1), $x_1$)
        })
      },
    )
  }),
)
$display(lim_(x -> x_0)) (f(x_1) - f(x_0)) / (x_1 - x_0)$, otteniamo una scrittura analoga di $f'(x_0)$, il cui valore corrisponde precisamente al coefficiente angolare della retta tangente a $f(x)$ in $x = x_0$. Quindi $r: y = f(x_0) + f'(x_0)(x - x_0)$.

#theorem(
  title: [Continuità di una funzione derivabile],
  [
    Siano $f: (a, b) -> RR$ e $x_0 in (a, b)$. Se $f$ è derivabile in $x_0$, allora è anche continua in $x_0$.
  ],
)
#proof([
  $f(x) - f(x_0) = (f(x) - f(x_0)) / (x - x_0) (x - x_0)$. Poiché $f(x) - f(x_0) display(-->_(x -> x_0)) 0$ e $x - x_0 display(-->_(x -> x_0)) 0$, allora $display(lim_(x -> x_0)) (f(x) - f(x_0)) = 0 <=> display(lim_(x -> x_0)) f(x) = f(x_0)$, quindi $f$ è continua in $x_0$.
])
#definition(
  title: [Funzione derivata],
  [
    Sia $f: (a, b) -> RR$ derivabile in $(a, b)$. Allora $forall x in (a, b) " " exists f'(x)$. Dunque abbiamo costruito la funzione $f': (a, b) -> RR$ detta _funzione derivata di $f$_.
  ],
)

#pagebreak()

== Calcolo di derivate fondamentali

$
  dif / (dif x) c = 0, c in RR "  " dif / (dif x) a x^n = a n x^(n - 1) "  " dif / (dif x) log_a (x) = (log_a e) / x, a > 0, a != 1
$
$ dif / (dif x) sin x = cos x "  " dif / (dif x) cos x = -sin x $
#proof([
  1. $display(lim_(h -> 0)) (f(x + h) - f(x)) / h = display(lim_(h -> 0)) (c - c) / h = display(lim_(h -> 0)) 0 / h = 0$
  3. $display(lim_(h -> 0)) (log_a (x + h) - log_a (x)) / h = display(lim_(h -> 0)) (log_a (x + h) / x) / h = display(lim_(h -> 0)) (log_a (1 + h / x)) / h = display(lim_(h -> 0)) 1 / x (log_a (1 + h / x)) / (h / x) = (log_a (e)) / x$

  4. $display(lim_(h -> 0)) (sin(x + h) - sin x) / h = display(lim_(h -> 0)) (sin x cos h + sin h cos x - sin x) / h = display(lim_(h -> 0)) (sin x ((cos h - 1) / h) + cos x ((sin h) / h)) = cos x$
])

#theorem(
  title: [Derivate di operazioni],
  [
    Siano $f$ e $g$ due funzioni derivabili in $x$. Allora:
    1. $f plus.minus g$ è derivabile in $x$ e $dif / (dif x) (f(x) plus.minus g(x)) = f'(x) plus.minus g'(x)$
    2. $f dot g$ è derivabile in $x$ e $dif / (dif x) f(x)g(x) = f'(x)g(x) + f(x)g'(x)$
    3. $f / g$ è derivabile in $x$ e $dif / (dif x) f(x) / g(x) = (f'(x)g(x) - f(x)g'(x)) / (g(x))^2$
  ],
)
#proof([
  1. $display(lim_(h -> 0)) (f(x + h) - g(x + h) - (f(x) + g(x))) / h = display(lim_(h -> 0)) (f(x + h) - f(x)) / h + display(lim_(h -> 0)) (g(x + h) - g(x)) / h = f'(x) + g'(x)$

  2. $display(lim_(h -> 0)) (f(x + h)g(x + h) - f(x)g(x)) / h = display(lim_(h -> 0)) (f(x + h)g(x + h) - f(x + h)g(x) + f(x + h)g(x) - f(x)g(x)) / h =$ \ $= display(lim_(h -> 0)) f(x + h) (g(x + h) - g(x)) / h + display(lim_(h -> 0)) g(x) (f(x + h) - f(x)) / h = f(x)g'(x) + f'(x)g(x)$
])

#theorem(
  title: [Derivata della funzione composta],
  [
    Siano $f$ e $g$ due funzioni derivabili. La funzione composta $f compose g$ è anch'essa derivabile e $dif / (dif x) f(g(x)) = f'(g(x))g'(x)$.
  ],
)

=== Derivate delle inverse
#theorem(
  title: [Derivata della funzione inversa],
  [
    Sia $f$ una funzione invertibile, continua con $f^(-1)$ anch'essa continua, derivabile in $x$ e tale che $f'(x) = 0$. Allora $f^(-1)$ è derivabile in $y$ e abbiamo che $f^(-1) (y) = lr(1 / (f'(x))|)_(x = f^(-1) (y))$
  ],
)
Possiamo scambiare $x$ e $y$, ottenendo $f^(-1) (x) = lr(1 / (f'(y))|)_(y = f^(-1) (x))$. Abbiamo dunque che:
- $a^x$ è l'inversa di $log_a (x)$, dove $a > 0, a != 1$ quindi
  $
    dif / (dif x) a^x = lr(1 / (dif / (dif x) log_a (y))|)_(y = a^x) = lr(1 / ((log_a e) / y)|)_(y = a^x) = a^x / (log_a e) = a^x log a
  $
#pagebreak()
- $x^alpha$ si può riscrivere come $e^log(x^alpha)$ dunque
  $
    dif / (dif x) = x^alpha = dif / (dif x) e^log(x^alpha) = dif / (dif x) e^(alpha log x) = e^(alpha log x) dot alpha dot 1 / x = x^alpha dot alpha / x = alpha x^(alpha - 1)
  $
- $arcsin x$ è l'inversa di $sin x$ allora
  $
    dif / (dif x) arcsin x = lr(1 / (dif / (dif x) sin y)|)_(y = arcsin x) = lr(1 / (cos y)|)_(y = arcsin x)
  $
  Poiché $cos y != 0$ in quanto a denominatore, allora $y != pi / 2, y != 3/2 pi$, ossia $y in (-pi / 2, pi / 2)$. Inoltre $sin^2 y + cos^2 y = 1$, quindi $cos y = sqrt(1 - sin^2 y) display(=^(y = arcsin x)) sqrt(1 - x^2)$, dunque
  $
    dif / (dif x) arcsin x = 1 / sqrt(1 - x^2), dif / (dif x) arccos x = -1 / sqrt(1 - x^2) "con" -1 < x < 1
  $
- $arctan x$ è l'inversa di $tan x$ quindi
  $
    dif / (dif x) arctan x = lr(1 / (tan y)|)_(y = arctan x) = lr(cos^2 y|)_(y = arctan x) <==>^(cos^2 y = 1 / (1 + tan^2 y)) 1 / (1 + tan^2 (arctan x)) = 1 / (1 + x^2)
  $
  Analogamente, si ha anche che
  $ dif / (dif x) "arccot" x = -1 / (1 + x^2) $

== Punti di non derivabilità

#definition(
  title: [Punto di non derivabilità],
  [
    Sia $f: (a, b) -> RR$ con $x_0 in (a, b)$. Se $exists.not display(lim_(x -> x_0)) (f(x) - f(x_0)) / (x - x_0)$ oppure vale $plus.minus infinity$, allora $x_0$ si dice _punto di non derivabilità_.
  ],
)
Se la funzione presenta punti di discontinuità, allora essi saranno anche punti di non derivabilità, quindi supponiamo ora che $f$ sia continua in $x_0$. Si ha che:
- Se $display(lim_(h -> 0^+)) (f(x_0 + h) - f(x_0)) / h != display(lim_(h -> 0^-)) (f(x_0 + h) - f(x_0)) / h$ ed entrambi i limiti sono finiti, allora $x_0$ è detto *punto angoloso*. Diciamo dunque che la *derivata destra*, ossia $f_+^' (x) := display(lim_(x -> x_0^+)) (f(x) - f(x_0)) / (x - x_0)$, e la *derivata sinistra*, ossia $f_-^' (x) := display(lim_(x -> x_0^-)) (f(x) - f(x_0)) / (x - x_0)$ sono diverse.
- Se $display(lim_(h -> 0)) (f(x_0 + h) - f(x_0)) / h = plus.minus infinity$, $x_0$ si dice *flesso a tangente verticale*
- Se $f_+^' (x_0) = plus.minus infinity$ e $f_-^' (x_0) = minus.plus infinity$, allora $x_0$ si dice *cuspide*

#align(center, grid(
  columns: 3,
  align: center + horizon,
  func(
    [$f(x) = abs(x)$ \ Punto angoloso in $x = 0$],
    (4, 3.87),
    (-2, 2),
    (
      x => calc.abs(x),
    ),
    y-min: -2,
    y-max: 2,
  ),
  func(
    [$f(x) = arctan x$ \ Flesso a tangente verticale in $x = 0$],
    (4, 3.87),
    (-100, 100),
    (x => calc.atan(x).rad(),),
    y-min: -3,
    y-max: 3,
  ),
  func(
    [$f(x) = sqrt(abs(x))$ \ Cuspide in $x = 0$],
    (4, 3.87),
    (-100, 100),
    (x => calc.sqrt(calc.abs(x)),),
    y-min: -15,
    y-max: 15,
  ),
))

== Estremi relativi

#definition(
  title: [Estremo relativo],
  [
    Sia $f: A -> RR$ con $A subset.eq RR$. $x_0 in A$ si dice _punto di massimo relativo_ o _locale_ di $f$ se $exists I(x_0) : f(x_0) >= f(x), forall x in A inter I(x_0)$. Viceversa, $x_0$ si dice _punto di minimo relativo_ o _locale_ di $f$ se $exists I(x_0) : f(x_0) <= f(x), forall x in A inter I(x_0)$. \
    $x_0$ si dice _punto di estremo relativo_ se è un punto di massimo o minimo relativo.
  ],
)
#note-box([
  Un estremo assoluto è anche un estremo relativo, ma non vale il contrario.
])
#definition(
  title: [Punto interno],
  [
    Sia $(a, b) subset RR$. Se $x_0 in (a, b)$, allora $x_0$ si dice _interno all'intervallo $(a, b)$_.
  ],
)
#definition(
  title: [Punto critico],
  [
    Sia $f: (a, b) -> RR$. $x_0 in (a, b)$ si dice _punto critico_ o _punto stazionario_ di $f$ se $exists f'(x_0) = 0$.
  ],
)

#theorem(
  title: [Teorema di Fermat],
  [
    Siano $f: (a, b) -> RR$ e $x_0 in (a, b)$ un punto di estremo relativo di $f$ tale che $f$ sia derivabile in $x_0$. Allora $x_0$ è un punto critico di $f$, ossia $f'(x_0) = 0$.
  ],
) <drv:fmt>
#proof([
  Supponiamo che $x_0$ sia un punto di massimo relativo. Poiché $x_0 in (a, b)$, $x_0$ è interno ad $(a, b)$. Allora $exists r > 0 : I_r (x_0) subset (a, b)$. Inoltre, poiché è un massimo, $f(x_0) >= f(x),$ \ $forall x in I_r (x_0)$. Consideriamo dunque il rapporto incrementale $(f(x_0 + h) - f(x_0)) / h$ con $abs(h) < r$: se $h > 0$ il rapporto vale $<= 0$, mentre se $h < 0$ il rapporto vale $>= 0$. Poiché $f$ è derivabile in $x_0$ per ipotesi, $exists display(lim_(h -> 0^+)) (f(x_0 + h) - f(x_0)) / h = display(lim_(h -> 0^-)) (f(x_0 + h) - f(x_0)) / h = f'(x_0)$. Per il @lmf:prmc, il limite destro vale $<= 0$ e il limite sinistro vale $>= 0$, quindi $f'(x_0) = 0$.
])

#warning-box([
  È essenziale che $x_0$ sia interno ad $(a, b)$ in quanto, se così non fosse, $x_0$ potrebbe essere un estremo relativo senza che $f'(x_0) = 0$. Inoltre, è essenziale che esista $f'(x_0)$ in quanto, altrimenti, l'estremo relativo potrebbe corrispondere ad un punto di non derivabilità. \
  Questo teorema implica che un estremo relativo sia anche un punto critico, e non il contrario.
])
#note-box([
  Questo teorema vale in particolare anche per gli estremi assoluti, purché siano verificate le ipotesi.
])
#pagebreak()

=== Problema di ottimizzazione

Sia $f: [a, b] -> RR$ una funzione continua in $[a, b]$. Per il @lmf:wst, $exists display(max_[a, b]) f$ e $exists display(min_[a, b]) f$, e possiamo calcolarli grazie al @drv:fmt. Sappiamo infatti che il $display(max_[a, b]) f$ e il $display(min_[a, b]) f$ possono trovarsi:
- agli *estremi* $a$ e $b$
- nei *punti di non derivabilità* di $f$, se esistono
- nei *punti critici* interni all'intervallo
Siccome, in genere, questi punti si trovano in numero finito, basterà calcolare il valore di $f$ in ognuno di questi punti e confrontarli: il più grande sarà il $display(max_[a, b]) f$, e il più piccolo sarà il $display(min_[a, b]) f$.

== Teoremi di Rolle e Lagrange

#theorem(
  title: [Teorema di Rolle],
  [
    Sia $f: [a, b] -> RR$ continua in $[a, b]$ e derivabile in $(a, b)$ tale che $f(a) = f(b)$. Allora \
    $exists xi in (a, b) : f'(xi) = 0$.
  ],
) <drv:rll>
#proof([
  Per ipotesi, $f$ è continua in $[a, b]$ quindi, per il @lmf:wst, $exists display(max_[a, b]) f, display(min_[a, b]) f$. Siano allora $x_M$ il punto di massimo assoluto e $x_m$ il punto di minimo assoluto di $f$. Possiamo avere che:
  - $x_M, x_m in {a, b}$, ossia che uno dei due o entrambi corrispondono agli estremi dell'intervallo, quindi abbiamo che $f(x_M) = f(x_m) <=> display(max_[a, b]) f = display(min_[a, b]) f$, quindi $f$ è costante su tutto $[a, b]$, ossia \ $f'(x) = 0, forall x in [a, b]$
  - almeno uno tra $x_M$ e $x_m$ cade dentro $(a, b)$, quindi, per il @drv:fmt, in tale punto $xi, f'(xi) = 0$.
])
#theorem(
  title: [Teorema di Lagrange],
  [
    Sia $f: [a, b] -> RR$ continua in $[a, b]$ e derivabile in $(a, b)$. Allora $exists xi in (a, b) : f'(xi) = (f(b) - f(a)) / (b - a)$.
  ],
) <drv:lgr>
#proof([
  Sia $g(x) = f(x) - (f(a) - (f(b) - f(a))/(b - a) (x - a)), forall x in [a, b] => g(x)$ è continua in $[a, b]$ e derivabile in $(a, b)$. Inoltre $g(a) = g(b) = 0$. Allora, per il @drv:rll, $exists xi in (a, b) : f'(xi) = 0$. $g'(x) = f'(x) - (f(b) - f(a)) / (b - a) <=> g'(xi) = f'(xi) - (f(b) - f(a)) / (b - a) = 0 <=> f'(xi) = (f(b) - f(a)) / (b - a)$
])
#warning-box([
  In entrambi i teoremi è essenziale considerare un intervallo e che la funzione sia derivabile su tutto esso, altrimenti le tesi potrebbero non verificarsi.
])

=== Applicazioni del teorema di Lagrange

#theorem(
  title: [Costanza di una funzione],
  [
    Sia $f$ una funzione derivabile nell'intervallo $I$. Se $f'(x) = 0, forall x in I$, allora $f$ è costante in $I$.
  ],
) <drv:cst>
#proof([
  Siano $x_1, x_2 in I$ con $x_1 < x_2$. Consideriamo l'intervallo $[x_1, x_2]$. Poiché $I$ è un intervallo, lo è anche $[x_1, x_2] subset.eq I$. Per il @drv:lgr, $exists xi in (x_1, x_2) : f'(xi) = (f(x_2) - f(x_1)) / (x_2 - x_1)$. Poiché $f'(xi) = 0$ per ipotesi, $f(x_2) - f(x_1) = 0 <=> f(x_2) = f(x_1)$. Poiché $x_1$ e $x_2$ sono arbitrari, $f$ è costante su tutto $I$.
])
#warning-box([
  È essenziale che $I$ sia un intervallo, altrimenti la derivata può sempre valere $0$ senza che la funzione sia costante, come per esempio la funzione $f(x) = [x]$.
])

#theorem(title: [Test di monotonia], [
  Sia $f$ una funzione derivabile nell'intervallo $I$. Allora:
  - $f$ è crescente se e solo se $f'(x) >= 0, forall x in I$
  - $f$ è decrescente se e solo se $f'(x) <= 0, forall x in I$.
  - $f$ è strettamente crescente se $f'(x) > 0, forall x in I$
  - $f$ è strettamente decrescente se $f'(x) < 0, forall x in I$
])
#proof([
  Supponiamo che $f$ sia crescente in $I$. Allora $(f(x) - f(x_0)) / (x - x_0) >= 0, forall x, x_0 in I, x != x_0$. Inoltre abbiamo che $f'(x_0) = display(lim_(x -> x_0)) (f(x) - f(x_0)) / (x - x_0)$, per il @lmf:prmc, vale $>= 0$. \
  Supponiamo ora che $f'(x) >= 0, forall x in I$. Siano $x_1, x_2 in I$ con $x_1 < x_2$. Per il @drv:lgr applicato a $[x_1, x_2] subset.eq I$, $exists xi in (x_1, x_2) : f'(xi) = (f(x_2) - f(x_1)) / (x_2 - x_1)$. Poiché $f'(x) >= 0, forall x in I$, allora $f'(xi) >= 0 <=> (f(x_2) - f(x_1)) / (x_2 - x_1) >= 0 <=> f$ è crescente in $I$.
])
#note-box([
  Da notare che la condizione di monotonia stretta non è necessaria e sufficiente ma solo sufficiente. Inoltre, in generale, non si può dire che una funzione sia crescente o decrescente nell'unione di due intervalli se essa stessa non è un intervallo.
])

#theorem(
  title: [Limite della derivata],
  [
    Sia $f: [a, b] -> RR$ continua in $[a, b]$ e derivabile in $[a, b] \\ {x_0}$. Se $exists display(lim_(x -> x_0)) f'(x) = L in RR$, allora $exists f'(x_0) = L$.
  ],
)
#proof([
  Per il @drv:lgr, $f'(xi) = (f(x_0 + h) - f(x_0)) / (h)$ per qualche $xi in (x_0, x_0 + h)$ se $h > 0$, o per qualche $xi in (x_0 + h, x_0)$ se $h < 0$. Abbiamo che $xi display(-->_(h -> 0^plus.minus)) x_0$, quindi $f'(xi) display(-->_(h -> 0^+)) f'(x_0)$. Allora $f'_+(x_0) = f'_-(x_0) = L$, dunque $f'(x_0) = L$.
])
#note-box([
  È anche vero che se $display(lim_(x -> x_0)) f'(x) = L_1, display(lim_(x -> x_0)) f'(x) = L_2$, allora $f'_+(x_0) = L_1, f'_-(x_0) = L_2$. In particolare, abbiamo che se $L_1 = plus.minus infinity, L_2 = plus.minus infinity$ o $L_1 != L_2$, allora $f$ non è derivabile in $x_0$.
])
#pagebreak()

== Derivate successive

Sia $f: (a, b) -> RR$ derivabile in $(a, b)$. La sua funzione derivata $f': (a, b) -> RR$ può essere a sua volta derivabile. Quindi la sua derivata è detta *derivata seconda* di $f$ e si indica $f''(x), D^2 f(x)$ o $(dif^2 f(x)) / (dif x^2)$. Questo processo è iterabile $n$ volte, definendo dunque la *derivata $n$-esima* $(dif^n f(x)) / (dif x^n)$, dove $n$ si dice *ordine di derivazione*.

#theorem(
  title: [Massimo e minimo relativo di una funzione],
  [
    Siano $f: (a, b) -> RR$ derivabile due volte in $(a, b), x_0 in (a, b)$ un punto critico di $f$. Se \
    $f''(x_0) > 0$, allora $x_0$ è un punto di minimo relativo, mentre se $f''(x_0) < 0$, allora $x_0$ è un punto di massimo relativo.
  ],
)

=== Convessità e concavità

#definition(
  title: [Funzione convessa e concava],
  [
    Una funzione $f: (a, b) -> RR$ con $x_1, x_2 in (a, b)$ si dice:

    - _convessa_ in $(a, b)$ se $f(x) <= f(x_1) + (f(x_2) - f(x_1)) / (x_2 - x_1) (x - x_1), forall x in [x_1, x_2]$

    - _concava_ in $(a, b)$ se $f(x) >= f(x_1) + (f(x_2) - f(x_1)) / (x_2 - x_1) (x - x_1), forall x in [x_1, x_2]$
  ],
)
#grid(
  columns: 2,
  [
    In termini geometrici, si intende che una funzione è convessa in un intervallo quando il grafico della funzione compreso tra due punti $P_1 = (x_1, f(x_1)), P_2 = (x_2, f(x_2))$ sta sotto il segmento $P_1 P_2$, ed è invece concava quando il grafico sta sopra tale segmento.
    #note-box([
      $f$ convessa in $(a, b) <=> -f$ concava in $(a, b)$
    ])
  ],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3.5, 3.5),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -5,
      y-max: 55,
      x-min: -5,
      x-max: 55,
      {
        plot.add(domain: (0.1, 65), x => 32 * calc.log(x))
        plot.add(
          domain: (6, 45),
          x => 32 * calc.log(x),
          style: (stroke: (paint: red)),
        )
        plot.annotate({
          content((20, 53), align(center, [è concava \ $arrow.r.curve$]))
        })
        plot.annotate({
          mark(
            (6, 32 * calc.log(6)),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
            scale: 12,
          )
          content((12, 32 * calc.log(6) - 4), $P_1$)
        })
        plot.annotate({
          mark(
            (45, 32 * calc.log(45)),
            0deg,
            anchor: "center",
            symbol: "o",
            fill: black,
            scale: 12,
          )
          content((50, 32 * calc.log(45) - 5), $P_2$)
        })
        plot.add-hline(32 * calc.log(6), min: 0, max: 6, style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-hline(32 * calc.log(45), min: 0, max: 45, style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-vline(6, min: 0, max: 32 * calc.log(6), style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add-vline(45, min: 0, max: 32 * calc.log(45), style: (
          stroke: (dash: "dashed", paint: red),
        ))
        plot.add(((6, 32 * calc.log(6)), (45, 32 * calc.log(45))), style: (
          stroke: (paint: black),
        ))

        plot.annotate({
          content((-10, 32 * calc.log(45)), $f(x_2)$)
          content((-10, 32 * calc.log(3)), $f(x_1)$)
          content((6, -5), $x_1$)
          content((45, -5), $x_2$)
        })
      },
    )
  }),
)

Un altro modo per riscrivere la disuguaglianza di convessità è il seguente:
$
  f(lambda x_1 + (1 - lambda) x_2) <= lambda f(x_1) + (1 - lambda) f(x_2), forall lambda in [0, 1]
$
Il primo termine della disuguaglianza rappresenta i punti tra $x_1$ e $x_2$, mentre il secondo le ordinate dei punti del segmento $P_1 P_2$.
#theorem(
  title: [Criterio del primo ordine],
  [
    Sia $f: (a, b) -> RR$ derivabile in $(a, b)$. Allora $f$ è:
    - convessa in $(a, b)$ se e solo se $f(x_2) >= f(x_1) + f'(x_1)(x_2 - x_1), forall x_1, x_2 in (a, b)$
    - concava in $(a, b)$ se e solo se $f(x_2) <= f(x_1) + f'(x_1)(x_2 - x_1), forall x_1, x_2 in (a, b)$
  ],
)
#theorem(
  title: [Criterio del secondo ordine],
  [
    Sia $f: (a, b) -> RR$ derivabile due volte in $(a, b)$. Allora $f$ è convessa in $(a, b)$ se e solo se \
    $f''(x) >= 0$, oppure è concava se e solo se $f''(x) <= 0, forall x in (a, b)$.
  ],
)
I punti in cui si passa dalla convessità alla concavità e viceversa si dicono *punti di flesso* o semplicemente *flessi*.

== Differenziabilità

#definition(
  title: [Funzione differenziabile],
  [
    Siano $f: (a, b) -> RR$ e $x_0 in (a, b)$. $f$ si dice _differenziabile_ in $x_0$ se
    $ exists lambda in RR : f(x) = f(x_0) + lambda (x - x_0) + o(x - x_0) $
  ],
)

Se una funzione $f(x)$ è differenziabile, si può definire una nuova funzione $d f(x_0): RR -> RR$ tale che $h |-> lambda h$ detta *differenziale di $f$ in $x_0$*.

#theorem(
  title: [Differenziabilità di una funzione derivabile],
  [
    Siano $f: (a, b) -> RR$ e $x_0 in (a, b)$. $f$ è differenziabile in $x_0$ se e solo se $f$ è derivabile in $x_0$.
  ],
)
#proof([
  Supponiamo che $f$ sia derivabile in $x_0$. Allora $exists f'(x_0) = display(lim_(x -> x_0)) (f(x) - f(x_0)) / (x - x_0)$. \
  $(f(x) - f(x_0)) / (x - x_0) - f'(x_0) display(-->_(x -> x_0)) 0$. Moltiplichiamo per $(x - x_0) / (x - x_0)$, allora $(f(x) - f(x_0) - f'(x_0)(x - x_0)) / (x - x_0) display(-->_(x -> x_0)) 0$ \
  $<=> f(x) - f(x_0) - f'(x_0)(x - x_0) = o(x - x_0) <=> f(x) = f(x_0) + f'(x_0)(x - x_0) + o(x - x_0)$. Quindi $f$ è differenziabile con $lambda = f'(x_0)$. \
  Supponiamo ora che $f$ sia differenziabile in $x_0$. Allora, per qualche $lambda in RR$, \ $f(x) = f(x_0) + lambda(x - x_0)+ o(x - x_0) <=> (f(x) - f(x_0)) / (x - x_0) = (lambda cancel(x - x_0)) / cancel(x - x_0) + underbrace(o(x - x_0) / (x - x_0), -> 0)$. Quindi, $(f(x) - f(x_0)) / (x - x_0) display(-->_(x - x_0)) lambda$, dunque, per definizione, $f'(x_0) display(-->_(x -> x_0)) lambda <=> exists f'(x_0) = lambda$.
])

== Teorema di de l'Hôpital

#theorem(
  title: [Teorema di de l'Hôpital],
  [
    Siano $f, g$ due funzioni derivabili in $(a, b) \\ {x_0}$ tali che $display(lim_(x -> x_0)) f(x) = display(lim_(x -> x_0)) g(x) = 0$. \ Se $g'(x) != 0, forall x in (a, b) \\ {x_0}$ e se $exists display(lim_(x -> x_0)) (f'(x)) / (g'(x))$, allora $exists display(lim_(x -> x_0)) f(x) / g(x) = display(lim_(x -> x_0)) (f'(x)) / (g'(x))$.
  ],
) <drv:lhp>

Questo teorema vale anche nei seguenti casi:
- si considerano i limiti per $x -> x_0^+$ o $x -> x_0^-$
- entrambe le funzioni sono infinite e non infinitesime, anche con segno discorde
- entrambe le funzioni sono derivabili in $(a, +infinity)$ quindi si considera $x -> +infinity$, oppure sono derivabili in $(-infinity, a)$ quindi si considera $x -> -infinity$
Il teorema di de l'Hôpital può essere utilizzato anche per risolvere forme indeterminate riconducibili a $0/0$ o $infinity/infinity$. Per esempio, sono equivalenti $underbrace(f(x), -> 0)underbrace(g(x), -> infinity)$ e $f(x) / underbrace(1 / g(x), -> 0)$, ma sulla seconda è applicabile il teorema.

#note-box([
  Va notato che $exists display(lim_(x -> x_0)) f(x) / g(x) arrow.r.double.not exists display(lim_(x -> x_0)) (f'(x)) / (g'(x))$. Per esempio $exists display(lim_(x -> +infinity)) (x + sin(x^2)) / (1 + x^2)$, ma $exists.not display(lim_(x -> +infinity)) (1 + 2x cos(x^2)) / (2x)$.
])

#pagebreak()

== Polinomio di Taylor

Consideriamo una funzione $f$ e il punto $P = (x_0, f(x_0))$. Possiamo dire che tra tutte le rette passanti per $P$, quella che meglio approssima il grafico di $f$ è la retta tangente a $f(x)$, ossia \
$y = f(x_0) + f'(x_0)(x - x_0)$. Quindi, tra tutti i polinomi di primo grado, $f(x)$ è meglio approssimata in un intorno di $x_0$ da $p_1 (x) = f(x_0) + f'(x_0)(x - x_0)$, dunque la funzione può essere scritta come $f(x) = p_1(x) + o(x - x_0)$. \
Supponiamo dunque che $f: (a, b) -> RR$ sia derivabile $n$ volte in $x_0$. Allora possiamo iterare il precedente ragionamento dicendo che:
$
  p_n (x) = f(x_0) + f'(x_0)(x - x_0) + (f''(x_0)) / 2! (x - x_0)^2 + ... + (f^((n))(x_0)) / n! (x - x_0)^n
$
Questo polinomio è detto *polinomio di Taylor di ordine $n$ e centro $x_0$*. Possiamo anche definire il *resto $n$-esimo* $R_n (x) = f(x) - p_n (x)$.

#theorem(
  title: [Formula di Taylor con resto di Peano],
  [
    Siano $f: (a, b) -> RR$ derivabile $n$ volte in $x_0$ e $x_0 in (a, b)$. Allora $f(x) = p_n (x) + R_n (x)$, dove $R_n (x) = o((x - x_0)^n)$.
  ],
)
#proof([
  Sia $n = 3$. Poiché $R_3 (x) = o((x - x_0)^3)$, allora $display(lim_(x -> x_0)) (R_3 (x)) / (x - x_0)^3 = 0 <=>$ \

  $display(lim_(x -> x_0)) (f(x) - p_3 (x)) / (x - x_0)^3 = 0 <=> display(lim_(x - x_0)) (f(x) - (f(x_0) + f'(x_0)(x - x_0) + (f''(x_0)) / 2! (x - x_0)^2 + (f'''(x_0))/3! (x - x_0)^3)) / (x - x_0)^3 = 0/0 => "FI"$ \
  Applichiamo il @drv:lhp. \

  $display(=^"H.") display(lim_(x -> x_0)) (f'(x) - (f'(x_0) + cancel(2)/cancel(2!) f''(x_0)(x - x_0) + 3 / 3! f'''(x_0)(x - x_0)^2)) / (3(x - x_0)^2) display(=^"H.") display(lim_(x -> x_0)) (f''(x_0) - (f''(x_0) + cancel(2 dot 3)/cancel(3!) f'''(x_0)(x - x_0))) / (6(x - x_0))$ \
  $= display(lim_(x -> x_0)) 1/6 ((f''(x) - f''(x_0)) / (x - x_0) - f'''(x_0)) = 1/6 (f'''(x_0) - f'''(x_0)) = 0 => R_3 (x) = o((x - x_0)^3)$
])

#note-box([
  Se $f$ è derivabile $n + 1$ volte in $(a, b)$ e $x_0 in (a, b)$, abbiamo un'alternativa al resto di Peano, ossia $R_n (x) = (f^((n + 1)) (xi) (x - x_0)^(n + 1)) / (n + 1)!$ per qualche $xi$ tra $x$ e $x_0$. Questo è detto *resto di Lagrange*. \
  Inoltre, per $x -> 0$, la formula di Taylor è detta anche *formula di MacLaurin*.
])

Di seguito, le formule di Taylor con $x -> 0$ per alcune funzioni elementari:
- $e^x = 1 + x + x^2/2! + x^3/3! + ... + x^n/n! + o(x^n)$
- $sin x = x - x^3/3! + x^5/5! - x^7/7! + ... + (-1)^n (x^(2n + 1))/(2n + 1)! + o(x^(2n + 2))$
- $cos x = 1 - x^2/2! + x^4/4! - x^6/6! + ... + (-1)^n x^(2n)/(2n)! + o(x^(2n + 1))$
- $1 / (1 - x) = 1 + x + x^2 + x^3 + ... + x^n + o(x^n)$
- $log(1 + x) = x - x^2/2 + x^3/3 - x^4/4 + ... + (-1)^n x^n/n + o(x^n)$
- $arctan x = x - x^3/3 + x^5/5 - x^7/7 + ... + (-1)^n x^(2n + 1)/(2n + 1) + o(x^(2n + 2))$

#note-box([
  Poiché le formule di Taylor di $sin x, cos x$ e $arctan x$ hanno termini a grado solo pari o dispari, si guadagna un grado dell'o-piccolo finale.
])

#pagebreak()

= Integrali

Sia $f: (a, b) -> RR$.
#definition(title: [Primitiva di una funzione], [
  Sia $F$ una funzione derivabile in $(a, b)$. $F$ si dice _primitiva_ o _antiderivata_ di $f$ se $F'(x) = f(x), forall x in (a, b)$.
])
#definition(title: [Integrale indefinito], [
  La totalità delle primitive di $f$ è detta _integrale indefinito_ di $f$, e si indica $integral f(x) dif x$.
])
#proposition(title: [Insieme delle primitive di una funzione], [
  Sia $F$ una primitiva di $f$ in $(a, b)$. Allora $integral f(x) dif x = F(x) + c$ al variare di $c in RR$.
])
#proof([
  Se $F(x)$ è una primitiva di $f$, allora $dif / (dif x) (F(x) + c) = f(x), forall c in RR$. \
  Sia ora $G(x)$ una qualsiasi primitiva di $f$. Allora $dif / (dif x) (G(x) - F(x)) = G'(x) - F'(x) =$ \
  $= f(x) - f(x) = 0, forall x in (a, b)$. \
  Per il @drv:cst, $exists c in RR : G(x) - F(x) = c, forall x in (a, b) <=> G(x) = F(x) + c$.
])

== Calcolo di integrali indefiniti

Dalle derivate delle funzioni elementari, possiamo ricavare i seguenti integrali immediati.
$
  integral k dif x = k x + c "  " integral x^alpha dif x = x^(alpha + 1) / (alpha + 1) + c, alpha != -1 "  " integral 1 / x dif x = log abs(x) + c "  " integral a^x dif x = a^x / (log a) + c
$
$
  integral 1 / (1 + x^2) dif x = arctan x + c "   " integral 1 / sqrt(1 - x^2) dif x = arcsin x + c "   " integral - 1 / sqrt(1 - x^2) dif x = arccos x + c
$
$
  integral sin x dif x = -cos x + c "  " integral cos x dif x = sin x + c "  " integral (1 + tan^2 x) dif x = integral 1/(cos^2 x) dif x = tan x + c
$
$
  integral 1/(sin^2 x) dif x = cot x + c "  " integral sinh x dif x = cosh x + c "  " integral cosh x dif x = sinh x + c "  " integral e^x dif x = e^x + c
$

L'integrale possiede la proprietà di *linearità*, quindi vale il seguente.
$
  integral (alpha f(x) + beta g(x)) dif x = alpha integral f(x) dif x + beta integral g(x) dif x, forall alpha, beta in RR
$

Dalla formula della derivata del prodotto di funzioni, possiamo arrivare alla formula dell'*integrazione per parti*. Per applicarla è necessario scegliere nell'espressione da integrare $f'(x)$ e $g(x)$, calcolare l'integrale della prima e la derivata della seconda e sostituire nella formula.
$
  dif / (dif x) f(x)g(x) = f'(x)g(x) + f(x)g'(x) <=> integral f'(x)g(x) dif x = f(x)g(x) - integral f(x)g'(x) dif x
$

Dalla formula della derivata della funzione composta (considerando $F$ una primitiva di $f$), si ha la formula dell'*integrazione per sostituzione*, ponendo $u = g(x)$ e $dif u = g'(x) dif x$.
$
  dif / (dif x) F(g(x)) = f(g(x))g'(x) <=> integral f(g(x))g'(x) = integral f(u) dif u = F(u) + c = F(g(x)) + c
$
Nella pratica, l'integrazione per sostituzione prevede che:
- si identifichi l'espressione $g(x)$ tale che venga sostituita da una variabile, ossia $u = g(x)$ e \ $dif u = g'(x) dif x$, ottenendo $integral f(g(x))g'(x) dif x = integral f(u) dif u = F(u) + c$
- si sostituisca $u = g(x)$ nell'espressione della primitiva $F(u)$
È anche possibile scambiare il ruolo di $u$ e $x$ se può risultare comodo, ottenendo dunque
$
  integral f(x) dif x = integral f(g(u))g'(u) dif u "con" x = g(u) <=> u = g^(-1) (x), dif x = g'(u) dif u
$
Quest'ultimo metodo permette di avere una lista di *integrali semi-immediati*, come per esempio:
$
  integral (g(x))^alpha g'(x) dif x = (g(x))^(alpha + 1) / (alpha + 1) + c "  " integral (g'(x)) / g(x) dif x = log abs(g(x)) + c "   " integral e^g(x) g'(x) dif x = e^g(x) + c
$

=== Integrazione di funzioni razionali

Consideriamo l'integrale $integral p(x)/q(x) dif x$. La strategia per calcolare questo tipo di integrali consiste nel ricondurre l'integrale in una forma tale per cui $deg(p(x)) < deg(q(x))$, ricorrendo alla divisione tra polinomi se già così non fosse ($p(x) / q(x) = s(x) + r(x) / q(x)$). Quando la frazione è ricondotta a questa forma, ci sono tre diverse strategie da applicare a seconda della situazione:
- $q(x)$ è *scomponibile* in polinomi irriducibili: si ricorre al metodo dei fratti semplici e si identificano i coefficienti dei numeratori (a seconda del $deg(q(x))$), la cui somma riporta alla frazione originale, come ad esempio $ integral (1 + 2x^2) / (x^4 - 1) dif x => x^4 - 1 = (x^2 - 1)(x^2 + 1) = (x - 1)(x + 1)(x^2 + 1) \
  <=> (1 + 2x^2) / (x^4 - 1) = A / (x - 1) + B / (x + 1) + (C x + D) / (x^2 + 1) =^(B = -A)_(C = 0) ((2A - D) + x^2(2A + D)) / (x^4 - 1) <=> cases(2A - D = 1, 2A + D = 2) " " cases(A = 3/4, D = 1/2) \
  <=> integral (1 + 2x^2) / (x^4 - 1) dif x = integral (3/4) / (x - 1) dif x - integral (3/4)/(x + 1) dif x + integral (1/2)/(x^2 + 1) dif x = 3/4 log abs((x - 1)/(x + 1)) + 1/2 arctan x + c $ Da notare che il numeratore della frazione con $x^2 + 1$ è un polinomio di 1° grado, poiché il numeratore deve differire dal denominatore di un solo grado.
- $q(x)$ è della forma $(x + k)^n$: si può integrare per sostituzione, ponendo $u = x + k$ e riscrivendo $p(x)$ in termini di $t$, oppure si ricorre sempre al metodo dei fratti semplici, considerando però un coefficente per ogni grado, ossia $A_1 / (x + k) + A_2 / (x + k)^2 + ... + A_n / (x + k)^n$
- $q(x)$ è già *irriducibile*: in questo caso si riconduce $p(x)$ alla forma $A q'(x) + B$, cosicché il primo termine avrà come risultato $log abs(q(x))$ e il secondo una variazione di $arctan x$, come ad esempio
  $
    integral (1 - 2x) / (x^2 + 2x + 5) dif x => Delta = 2^2 - 4 dot 5 = 4 - 20 = - 16 => q(x) "non ha radici in" RR \
    <=> 1 - 2x = A q'(x) + B = A(2x + 2) + B = 2A x + 2A + B <=> cases(2A = -2, 2A + B = 1) " " cases(A = -1, B = 3) \
    integral (1 - 2x) / (x^2 + 2x + 5) dif x = -1 integral (2x + 2) / (x^2 + 2x + 5) dif x + integral 3 / (x^2 + 2x + 5) dif x = log abs(x^2 + 2x + 5) + I \
    I = integral 3 / (x^2 + 2x + 5) dif x = 3 integral 1 / ((x^2 + 2x + 1) + 4) dif x = 3 integral 1 / (4((x + 1)^2 / 4 + 1)) dif x = 3/4 dot 2 integral (1/2) / (((x+ 1) / 2)^2 + 1) dif x \
    = 3/2 arctan((x + 1) / 2) + c <=> integral (1 - 2x) / (x^2 + 2x + 5) dif x = log(x^2 + 2x + 5) + 3/2 arctan((x + 1) / 2) + c
  $

== Integrali definiti

#grid(
  columns: 2,
  [Sia $f: [a, b] -> RR$ una funzione limitata. Allora $exists M, m in RR : m <= f(x) <= M, forall x in [a, b]$. Consideriamo il sottografico di $f$ $cal(S) := {(x, y) in RR^2 : a <= x <= b, 0 <= y <= f(x)}$. L'area di $cal(S)$ può essere calcolata pensando di dividere $[a, b]$ in intervalli più piccoli, ossia in *partizioni* $cal(P)$ di $[a, b]$, tali che $a = x_0 < x_1 < x_2 < ... < x_n = b$ per un qualche $n in NN$. \ Dunque, per $k = 0, ..., n$, possiamo definire $M_k := display(sup_[x_(k - 1), x_k]) f$ e $m_k := display(inf_[x_(k - 1), x_k]) f$. Possiamo considerare che ogni partizione, permette di visualizzare 2 rettangoli, entrambi con larghezza $x_k - x_(k - 1)$ mentre uno
  ],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3.5, 3.5),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -1,
      y-max: 15,
      x-min: -1,
      x-max: 10,
      {
        let f = x => 0.05 * (x - 4) * (x - 5) * (x - 4) + 8
        plot.add(domain: (1, 9), f, style: (stroke: red))
        plot.annotate({
          rect((1, 0), (3, f(1)), stroke: green, fill: green.opacify(-80%))
          rect((3, 0), (5, f(3)), stroke: green, fill: green.opacify(-80%))
          rect((5, 0), (7, f(5)), stroke: green, fill: green.opacify(-80%))
          rect((7, 0), (9, f(7)), stroke: green, fill: green.opacify(-80%))
          rect((1, f(1)), (3, f(3)), stroke: blue, fill: blue.opacify(-80%))
          rect((3, f(3)), (5, f(5)), stroke: blue, fill: blue.opacify(-80%))
          rect((5, f(5)), (7, f(7)), stroke: blue, fill: blue.opacify(-80%))
          rect((7, f(7)), (9, f(9)), stroke: blue, fill: blue.opacify(-80%))
          content((1, -1), $a$)
          content((3, -1), $x_1$)
          content((5, -1), $x_2$)
          content((7, -1), $x_3$)
          content((9, -1), $b$)
          content((11, 4), text(green)[$s(cal(P))$])
          content((11, 10.5), text(blue)[$S(cal(P))$])
          content((11, 14.5), text(red)[$f(x)$])
        })
      },
    )
  }),
)

ha altezza $M_k$ e l'altro $m_k$. Se consideriamo la somma delle patrizioni, otteniamo
$
  S(cal(P)) = display(sum^n_(k = 1)) M_k (x_k - x_(k - 1)) "    " s(cal(P)) = display(sum^n_(k = 1)) m_k (x_k - x_(k - 1))
$
La prima è la somma delle aree massime dei rettangoli ed è detta *somma integrale superiore* e la seconda considera invece le aree minime dei rettangoli ed è detta *somma integrale inferiore*. Abbiamo dunque che $s(cal(P)) <= S(cal(P))$. \
La somma integrale può essere definita anche in termini di $f$.
$
  S(f) := inf{S(cal(P)) : cal(P) "partizione di" [a, b]}, s(f) := sup{S(cal(P)) : cal(P) "partizione di" [a, b]} => s(f) <= S(f)
$

#definition(title: [Funzione integrabile secondo Riemann], [
  Sia $f: [a, b] -> RR$. $f$ si dice _integrabile secondo Riemann_ in $[a, b]$ se $s(f) = S(f)$.
])
#definition(title: [Integrale definito], [
  Sia $f$ integrabile in $[a, b]$. Allora $integral_a^b f(x) dif x := s(f) = S(f)$ è detto _integrale definito di $f$_ in $[a, b]$.
])
#note-box([
  Se $f(x) >= 0, forall x in [a, b]$, $integral_a^b f(x) dif x$ rappresenta l'area del sottografico $cal(S)$.
])

#theorem(title: [Integrabilità di una funzione continua], [
  Sia $f: [a, b] -> RR$. Se $f$ è continua in $[a, b]$, allora è integrabile in $[a, b]$.
])
#theorem(title: [Integrabilità di una funzione monotòna e limitata], [
  Sia $f: [a, b] -> RR$. Se $f$ è monotòna in $[a, b]$ e limitata, allora è integrabile in $[a, b]$.
])

=== Proprietà degli integrali definiti

Siano $f, g$ due funzioni integrabili in $[a, b]$. Allora abbiamo le seguenti proprietà:
- $f plus.minus g$ è integrabile in $[a, b]$ e $integral_a^b (f(x) plus.minus g(x)) dif x = integral_a^b f(x) dif x plus.minus integral_a^b g(x) dif x$
- $alpha f$ è integrabile in $[a, b], forall alpha in RR$ e $integral_a^b alpha f(x) dif x = alpha integral_a^b f(x) dif x$
- se $f <= g$ in $[a, b]$ allora $integral_a^b f(x) dif x <= integral_a^b g(x) dif x$
- se $c in [a, b]$ allora $integral_a^b f(x) dif x = integral_a^c f(x) dif x + integral_c^b f(x) dif x$
- $integral_a^a f(x) dif x = 0$
- $integral_a^b f(x) dif x = -integral_b^a f(x) dif x$
- se $a > b$, poiché $integral_a^b f(x) dif x <= integral_a^b abs(f(x)) dif x$ e $integral_a^b f(x) >= -integral_a^b abs(f(x))$, abbiamo \ $- integral_a^b abs(f(x)) dif x <= integral_a^b f(x) dif x <= integral_a^b abs(f(x)) dif x$, ossia $abs(integral_a^b f(x) dif x) <= integral_a^b abs(f(x)) dif x$

#note-box([
  Nel caso in cui non sia noto che $a > b$, si ha in generale $abs(integral_a^b f(x) dif x) <= abs(integral_a^b abs(f(x)) dif x)$.
])

#theorem(title: [Teorema della media integrale], [
  Siano $f$ integrabile in $[a, b], m := display(inf_[a, b]) f in RR$ e $M := display(sup_[a, b]) f in RR$. Allora:
  - $m(b - a) <= integral_a^b f(x) dif x <= M(b - a)$
  - se $f$ è continua in $[a, b]$, $exists xi in [a, b] : integral_a^b f(x) dif x = f(xi)(b - a)$
]) <int:med>
#proof([
  Per ipotesi, $m <= f(x) <= M, forall x in [a, b]$. Integrando su $[a, b]$, si ha \
  $integral_a^b m dif x <= integral_a^b f(x) dif x <= integral_a^b M dif x <=> m(b - a) <= integral_a^b f(x) dif x <= M(b - a)$. \
  Sia $f$ continua in $[a, b]$. Per la precedente relazione, $m <= (integral_a^b f(x) dif x) / (b - a) <= M$, quindi $(integral_a^b f(x) dif x) / (b - a) in [m, M]$. Per il @lmf:vim, $exists xi in [a, b] : f(xi) = (integral_a^b f(x) dif x) / (b - a) <=> integral_a^b f(x) dif x = f(xi)(b - a)$.
])

#definition(title: [Funzione integrale], [
  Sia $f$ integrabile in $[a, b]$. Allora $F(x) := integral_a^x f(t) dif t, forall x in [a, b]$ è detta _funzione integrale_ di $f$.
])
#theorem(title: [Teorema fondamentale del calcolo integrale], [
  Sia $f$ continua in $[a, b]$. Allora:
  1. la sua funzione integrale $F(x)$ è derivabile e $F'(x) = f(x)$
  2. se $G$ è una primitiva di $f$ in $[a, b]$, allora $F(x) = G(x) - G(a), forall x in [a, b]$. In particolare, $integral_a^b f(x) dif x = G(b) - G(a), forall x in [a, b]$
]) <int:fci>
#proof([
  1. Siano $x in [a, b], x + h in [a, b]$. Allora $(F(x + h) - F(x)) / h = 1/h (integral_a^(x + h) f(t) dif t - integral_a^h f(t) dif t)$ $= 1/h (cancel(integral_a^x f(t) dif t) + integral_x^(x + h) f(t) dif t - cancel(integral_a^x f(t) dif t)) = 1/h integral_x^(x + h) f(t) dif t$. Quindi, poiché $f$ è continua in $[a, b]$, per il @int:med, $exists xi in (x, x + h) : 1/h integral_x^(x + h) f(t) dif t = f(xi)$. Poiché $x < xi < x + h$, \ $xi display(-->_(h -> 0)) x$ e, poiché $f$ è continua, $f(xi) display(-->_(h -> 0)) f(x)$, quindi $(F(x + h) - F(x)) / h display(-->_(h -> 0)) f(x) <=> F'(x) = f(x)$. \
  2. Sia $G$ una primitiva di $f$. Allora $G'(x) - F'(x) = f(x) - f(x) = 0, forall x in [a, b]$, quindi, per il @drv:cst, $G(x) - F(x)$ è costante in $[a, b]$. Abbiamo che $c = G(x) - F(x) = G(a) - F(a) = G(a) - 0 = G(a), forall x in [a, b] => F(x) = G(x) - G(a)$, poiché $F(a) = integral_a^a f(t) dif t = 0$. Se poniamo $x = b$, otteniamo $integral_a^b f(t) dif t = F(b) = G(b) - G(a)$.
])

=== Calcolo di integrali definiti

Per calcolare $integral_a^b f(x) dif x$, utilizziamo il @int:fci:
- si trova una primitiva $G(x)$ di $f(x)$
- si calcola $lr(G(x)|)_a^b = G(b) - G(a)$, il quale è il nostro risultato
Il calcolo risulta più intricato, quando è necessaria l'integrazione per sostituzione. Infatti, possiamo calcolare $integral_a^b f(x) dif x$ in due modi principali:
- se integriamo nella forma $integral_a^b f(x) dif x = integral f(g(u))g'(u) dif u$ con $x = g(u)$ otteniamo che
  $
    &"se" g arrow.tr, "ossia" g' > 0 " " => integral_a^b f(x) dif x = integral_(g^(-1) (a))^(g^(-1) (b)) f(g(u))g'(u) dif u \
    &"se" g arrow.br, "ossia" g' < 0 " " => integral_a^b f(x) dif x = integral_(g^(-1) (b))^(g^(-1) (a)) f(g(u))g'(u) dif u = integral_(g^(-1) (a))^(g^(-1) (b)) f(g(u))(-g'(u)) dif u
  $
  $
    <==> integral_a^b f(x) dif x = integral_(g^(-1) (a))^(g^(-1) (b)) f(g(u))abs(g'(u)) dif u
  $
- se integriamo nella forma $integral f(g(x)) dif x = integral f(u) dif u$ con $u = g(x)$ otteniamo che
  $ integral_a^b f(g(x))g'(x) dif x = integral_(g(a))^(g(b)) f(u) dif u $

=== Aree di regioni piane

#grid(
  columns: 2,
  [
    Siano $f, g$ integrabili in $[a, b]$. Consideriamo $H := {(x, y) in RR^2 : x in [a, b], g(x) <= y <= f(x)}$. Se $f >= g$ in $[a, b]$, allora abbiamo che
    $
      "area"(H) = integral_a^b f(x) dif x - integral_a^b g(x) dif x = integral_a^b (f(x) - g(x)) dif x
    $
  ],
  cetz.canvas({
    import cetz.draw: *
    import cetz-plot: plot
    plot.plot(
      size: (3.5, 3.5),
      axis-style: "school-book",
      x-tick-step: none,
      y-tick-step: none,
      y-min: -1,
      y-max: 15,
      x-min: -1,
      x-max: 10,
      {
        let f = x => 0.05 * (x - 4) * (x - 5) * (x - 4) + 10
        let g = x => 0.05 * (x - 2) * (x - 3) * (x - 8) + 5
        plot.add-vline(1, min: 0, max: f(1), style: (
          stroke: (paint: red, dash: "dashed"),
        ))
        plot.add-vline(9, min: 0, max: f(9), style: (
          stroke: (paint: red, dash: "dashed"),
        ))
        plot.add-fill-between(domain: (1, 9), f, g, style: (
          stroke: (paint: red),
          fill: red.opacify(-80%),
        ))
        plot.annotate({
          content((1, -1), $a$)
          content((9, -1), $b$)
          content((11, 16.5), text(red)[$f(x)$])
          content((11, 8.5), text(red)[$g(x)$])
          content((5, 7.5), text(red)[$H$])
        })
      },
    )
  }),
)

== Integrali impropri

Sia $f: (a, b] -> RR$ continua in $(a, b]$ e non limitata con un asintoto verticale in $x = a$. \
Consideriamo $alpha in (a, b]$. Sappiamo che $forall alpha in (a, b]$ $f$ è integrabile in $[alpha, b]$, quindi $integral_alpha^b f(x) dif x in RR$, quindi possiamo dire che $f$ è integrabile *in senso improprio* in $[a, b]$ se $exists display(lim_(alpha -> a^+)) integral_alpha^b f(x) dif x$, ossia poniamo $integral_a^b f(x) dif x = display(lim_(alpha -> a^+)) integral_alpha^b f(x) dif x$:
- se questo limite esiste ed è reale, si dice che l'integrale *converge*
- se questo limite va all'infinito o non esiste, diciamo che $f$ *non è integrabile in senso improprio* in $[a, b]$, quindi non converge o diverge
Lo stesso ragionamento vale se considero l'intervallo $[a, b)$ con un asintoto verticale in $x = b$, oppure se uno dei due estremi dell'intervallo è infinito ($(infinity, a]$ o $[a, infinity)$).

=== Criteri di convergenza

#theorem(title: [Teorema del confronto], [
  Siano $f, g: [a, +infinity) -> RR$ continue in $[a, +infinity)$ tale che $f, g >= 0$ in $[a, +infinity)$. Allora:
  - se $f(x) <= g(x)$ e $g$ è integrabile in senso improprio in $[a, +infinity)$, allora $f$ è integrabile in senso improprio e $integral_a^(+infinity) f(x) dif x <= integral_a^(+infinity) g(x) dif x$
  - se $f(x) >= g(x)$ e $integral_a^(+infinity) g(x) dif x = +infinity$, allora $integral_a^(+infinity) f(x) dif x = +infinity$
]) <int:cfr>
#proof([
  Siano $F(t) := integral_a^t f(x) dif x, G(t) := integral_a^t g(x) dif x, forall t >= a$. Per ipotesi, $F(t) <= G(t)$.
  Poiché $f >= 0, g >= 0$, allora $F$ e $G$ sono crescenti, quindi $exists display(lim_(t -> infinity)) F(t), display(lim_(t -> +infinity)) G(t)$. Poiché $g$ è integrabile, $display(lim_(t -> +infinity)) = integral_a^(+infinity) g(x) dif x in RR$, quindi, visto che $F(t) <= G(t)$, anche $f$ è integrabile e $display(lim_(t -> +infinity)) F(t) = integral_a^b f(x) dif x$.
])

Questo teorema vale anche per $(-infinity, a]$ e $integral_a^b f(x) dif x$ con un asintoto verticale per $x = a$ o $x = b$.

#theorem(title: [Teorema del confronto asintotico], [
  Siano $f, g: [a, +infinity) -> RR$ continue in $[a, +infinity)$ con $f, g >= 0$. Sia $display(lim_(x -> +infinity)) f(x) / g(x) = L$ dove \
  $L in [0, +infinity]$. Allora:
  - se $L in RR \\ {0}$, $integral_a^(+infinity) f(x) dif x$ e $integral_a^(+infinity) g(x) dif x$ hanno lo stesso carattere
  - se $L = 0$ e $integral_a^(+infinity) g(x) dif x$ converge, anche $integral_a^(+infinity) f(x) dif x$ converge
  - se $L = +infinity$ e $integral_a^(+infinity) g(x) dif x$ diverge, anche $integral_a^(+infinity) f(x) dif x$ diverge
])
Se abbiamo $integral_(-infinity)^a f(x) dif x$, consideriamo il limite per $x -> -infinity$, mentre se abbiamo $(a, b]$ o $[a, b)$, consideriamo il limite per $x$ che tende al valore per il quale l'intervallo è aperto.

=== Convergenza assoluta

Sia $f: [a, +infinity) -> RR$ continua in $[a, +infinity)$. Allora anche $abs(f)$ è continua in $[a, +infinity)$, quindi $integral_a^alpha abs(f(x)) dif x in RR, forall alpha > a$. Diremo che l'integrale $integral_a^(+infinity) f(x) dif x$:
- *converge assolutamente* se $exists lim_(alpha -> +infinity) integral_a^alpha abs(f(x)) dif x in RR$
- *diverge assolutamente* se $lim_(alpha -> +infinity) integral_a^alpha abs(f(x)) dif x = +infinity$

#theorem(title: [Carattere di una funzione assolutamente integrabile], [
  Sia $f: [a, +infinity) -> RR$ continua in $[a, +infinity)$. Se $abs(f)$ è integrabile in senso improprio, allora anche $f$ lo è e risulta che $abs(integral_a^(+infinity) f(x) dif x) <= integral_a^(+infinity) abs(f(x)) dif x$.
])
#proof([
  Siano $f^+ (x) = max {f(x), 0}, f^- (x) = max {-f(x), 0}$. Abbiamo dunque che $0 <= f^+ (x) <= abs(f(x)), 0 <= f^- (x) <= abs(f(x)), forall x in [a, +infinity)$. Per il @int:cfr, poiché $abs(f)$ è integrabile in senso improprio in $[a, +infinity)$, anche $f^+$ e $f^-$ lo sono. Poiché $f(x) = f^+ (x) - f^- (x)$, allora $integral_a^(+infinity) f(x) dif x = integral_a^(+infinity) (f^+ (x) - f^- (x)) dif x = integral_a^(+infinity) f^+ (x) dif x - integral_a^(+infinity) f^- (x) dif x = c_1 - c_2$. Visto che $c_1, c_2 in RR^+, c_1 - c_2 in RR$, quindi $f$ è integrabile in senso improprio. \
  $abs(integral_a^(+infinity) f(x) dif x) = abs(integral_a^(+infinity) f^+ (x) dif x - integral_a^(+infinity) f^- (x) dif x)$ e $abs(integral_a^(+infinity) f^+ (x) dif x) + abs(integral_a^(+infinity) f^- (x) dif x) = integral_a^(+infinity) f^+ (x) dif x + integral_a^(+infinity) f^- (x) dif x = integral_a^(+infinity) (f^+ (x) + f^- (x)) dif x = integral_a^(+infinity) abs(f(x)) dif x$, poiché \
  $abs(f(x)) = f^+ (x) + f^- (x)$. Quindi $abs(integral_a^(+infinity) f(x) dif x) <= integral_a^(+infinity) abs(f(x)) dif x$
])

#theorem(title: [Criterio integrale per serie], [
  Sia $f: [1, +infinity) -> RR$ continua e decrescente con $f >= 0$. Allora $integral_a^(+infinity) f(x) dif x$ e $display(sum^infinity_(n = 1)) f(n)$ hanno lo stesso carattere.
])
#warning-box([
  La convergenza semplice non implica la convergenza assoluta. Per esempio $integral_0^(+infinity) (sin x) / x dif x$ converge, ma $integral_0^(+infinity) abs((sin x) / x) dif x$.
])

