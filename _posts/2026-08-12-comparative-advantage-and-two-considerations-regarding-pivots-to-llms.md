---
title: Comparative advantage and two considerations regarding pivots to LLMs
description: >-
  Besides asking which LLM-related topics are closest to your existing
  expertise, ask which topics are far from everyone's existing expertise.
date: 2026-08-12 00:00:00 +0000
how_written: >-
  I gave the main idea(s) and spent some time on iteration, even hand-edited a
  bunch. Thought about putting it on my blog, but then felt like it wasn't
  _that_ interesting.
---

In 2020, few researchers worked on LLMs. By 2024, the importance of LLMs had become clear and so it was clear that (whatever perspective you're taking -- realizing benefits or addressing risks) a lot more people should work on LLMs. So a large number of researchers, trained on all sorts of pre-LLM topics, faced the question: what LLM-related work (if any) should I move to?

## The obvious pivot: from X to X with LLMs

The most salient option: keep doing what you have been doing, but with or for LLMs. Many actual pivots fit this description. Chris Olah and other mechanistic interpretability researchers used to reverse-engineer vision models (identifying, e.g., curve-detector neurons). They now reverse-engineer LLMs (identifying, e.g., induction heads). Noam Brown made poker AIs (and later a Diplomacy AI) stronger by giving them more compute at decision time. He then joined OpenAI to work on inference-time scaling for LLMs, i.e., on what became reasoning models. Multi-agent RL researchers now study systems of interacting LLM agents.

You can view these pivots as being driven by comparative advantage considerations: LLM research includes tasks that closely resemble pre-LLM work, and whoever did the pre-LLM version is best positioned to do the LLM version, because their skills, methods, and stock of research questions transfer. If you have spent years administering political-attitude surveys to humans, you know the instruments and their pitfalls better than anyone else who might administer them to LLMs.

## A less obvious pivot consideration

Picture the space of possible LLM-related research topics. Each researcher sits at some distance from each topic, where the distance measures how little of their existing expertise carries over to that topic. The most obvious approach (in line with the above pivot from X to X-with-LLMs) is to pivot to whatever topic is closest to you.

But from a comparative advantage perspective, when you consider pivoting to a given topic, two distances matter: your distance to the topic, and everyone else's. If a topic is of the form X with LLMs for some established research area X, then a whole field sits close to that topic and will predictably move into it.

Some topics, however, aren't of this form and aren't particularly close to any existing pre-LLM area. Making LLMs better at philosophy is my favorite example. Nobody worked on making pre-LLM AIs better at philosophy, because it's hard to imagine pre-LLM AI systems doing any philosophy at all. Consequently, no field can pivot into this topic the way multi-agent RL researchers can pivot into multi-agent LLM research. Everyone starts far from it. So even if it's not the closest-to-you research topic, you should consider picking it up.

![Researchers and LLM-related topics drawn as points in a plane](/assets/img/llm-topic-distances.svg){: width="1366" height="780" }
_Researchers (black dots) and LLM-related topics (colored diamonds); distance represents how little expertise carries over. The blue topic – “X with LLMs” – is closer to you (orange dot) than the pink topic, but the researchers of field X are much closer to it than you are. The pink topic is farther from you – yet it is far from everyone else as well, so nobody has a head start on you._

Empirical assessment of catastrophic AI risk is a less clean example. Some researchers anticipated the problem long before LLMs, so a neighboring community already existed. But they had no systems on which to study fairly direct versions of questions such as whether a capable AI would pursue goals across situations, deceive its overseers, or try to gain control; empirical work had to rely on distant proxies. LLMs made such questions substantially more accessible. Here the question predates LLMs, but a reasonably direct empirical object did not.

Some forms of chain-of-thought-related research (to what extent CoT is faithful, whether we can use it to reliably oversee models' thinking) might be another candidate. While explainable AI and mechanistic interpretability sit nearby, I don't think other kinds of trained models give you analogous, seemingly interpretable records of their computations by default (without any sort of decoding step).

So besides the obvious question – which LLM-related topics am I closest to? – a prospective pivoter should ask the less obvious question: which LLM-related topics are far from everyone's existing work? (Of course, besides comparative advantage, other things should influence whether you choose to work on a topic, such as how important that topic is.)
