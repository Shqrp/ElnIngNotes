#import "@preview/cetz:0.4.2"
#import "@preview/cetz-plot:0.1.3"
#import "@preview/theorion:0.4.1": *
#import "@preview/itemize:0.2.0" as el

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

#let polypst(
  title,
  subtitle,
  reversePageHeader: false,
  demIndex: false,
) = body => {
  show: show-theorion
  show: el.default-enum-list

  set text(lang: "it")
  set par(justify: true)
  set page(numbering: "I", footer: [], header: context {
    if counter(page).display() != "I" {
      if not (calc.even(counter(page).get().at(0)) or not reversePageHeader) {
        align(
          left,
          [#{ counter(page).display() } - _#{ title }_],
        )
      } else {
        align(
          right,
          [_#{ title }_ - #{ counter(page).display() }],
        )
      }
    }
  })

  align(center, heading(
    outlined: false,
    title,
  ))
  align(
    center,
    subtitle,
  )

  set heading(numbering: "1.1.")
  set-theorion-numbering("1.1")
  outline(title: [Indice])

  pagebreak()
  counter(page).update(1)
  set page(numbering: "1")

  body

  if demIndex {
    pagebreak()
    outline(
      title: [Indice dei dimostrabili],
      target: figure
        .where(kind: "theorem")
        .or(figure.where(kind: "proposition"))
        .or(figure.where(kind: "lemma")),
    )
  }
}

