use super::{event::Event, parser::Parse, parser_error::ParseError, syntax::AsukaLanguage};
use crate::compiler::parse::lexer::Token;
use rowan::{GreenNodeBuilder, Language};
use std::mem;

pub(super) struct Sink<'l, 't> {
    builder: GreenNodeBuilder<'static>,
    tokens: &'l [Token<'t>],
    cursor: usize,
    events: Vec<Event>,
    errors: Vec<ParseError>,
}

impl<'l, 't> Sink<'l, 't> {
    pub(super) fn new(tokens: &'l [Token<'t>], events: Vec<Event>) -> Self {
        Self {
            builder: GreenNodeBuilder::new(),
            tokens,
            cursor: 0,
            events,
            errors: Vec::new(),
        }
    }

    pub(super) fn finish(mut self) -> Parse {
        for idx in 0..self.events.len() {
            match mem::replace(&mut self.events[idx], Event::Placeholder) {
                Event::AddToken => self.token(),
                Event::StartNode {
                    kind,
                    forward_parent,
                } => {
                    let mut kinds = vec![kind];

                    let mut idx = idx;
                    let mut forward_parent = forward_parent;

                    // Walk through the forward parent of the forward parent, and the forward parent
                    // of that, and of that, etc. until we reach a StartNode event without a forward
                    // parent.
                    while let Some(fp) = forward_parent {
                        idx += fp;

                        forward_parent = if let Event::StartNode {
                            kind,
                            forward_parent,
                        } =
                            mem::replace(&mut self.events[idx], Event::Placeholder)
                        {
                            kinds.push(kind);
                            forward_parent
                        } else {
                            unreachable!()
                        };
                    }

                    for kind in kinds.into_iter().rev() {
                        self.builder.start_node(AsukaLanguage::kind_to_raw(kind));
                    }
                }
                Event::StartNodeAt {
                    kind: _,
                    checkpoint: _,
                } => unreachable!(),
                Event::FinishNode => self.builder.finish_node(),
                Event::Placeholder => {}
                Event::Error(error) => self.errors.push(error),
            }
            self.eat_trivial();
        }
        Parse {
            green_node: self.builder.finish(),
            errors: self.errors,
        }
    }

    fn eat_trivial(&mut self) {
        while let Some(token) = self.tokens.get(self.cursor) {
            if !token.kind.is_trivial() {
                break;
            }

            self.token();
        }
    }
    fn token(&mut self) {
        let Token { kind, text, .. } = self.tokens[self.cursor];
        self.builder
            .token(AsukaLanguage::kind_to_raw(kind), text.into());
        self.cursor += 1;
    }

    fn error(&mut self, err: ParseError) {
        todo!()
    }
}
