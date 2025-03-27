#import "template.typ": *

#show: acmart.with(
  format: "acmsmall", title: "The Name of the Title is Hope", shortauthors: "Sun et al.", authors: {
    let northeastern = (
      institution: "Northeastern University", city: "Boston", state: "Massachusetts", country: "USA", postcode: "02115",
    )
    (
      (
        name: "Yifei Sun", email: "ysun@ccs.neu.edu", orcid: "0000-0002-1591-7458", affiliation: northeastern,
      ), (
        name: "Ji-Yong Shin", email: "j.shin@northeastern.edu", orcid: "0000-0002-1595-4849", affiliation: northeastern,
      ),
    )
  }, abstract: [
    A clear and well-documented Typst document is presented as an article formatted
    for publication by ACM in a conference proceedings or journal publication. Based
    on the "acmart" template, this article presents and explains many of the common
    variations, as well as many of the formatting elements an author may use in the
    preparation of the documentation of their work.
  ],
  // ccs: (
  //   ([Computer systems organization], (
  //       (500, [Embedded systems]),
  //       (300, [Redundancy]),
  //       (0,   [Robotics]))),
  //   ([Networks], (
  //       (100, [Network reliability]),))
  // ),
  // keywords: ("datasets", "neural networks", "gaze detection", "text tagging"),
  copyright: "acmlicensed", acmJournal: "JACM", acmVolume: 37, acmNumber: 4, acmArticle: 111, acmMonth: 8, acmYear: 2018,
)

#include "introduction.typ"
#include "references.typ"
