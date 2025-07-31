#[derive(Debug, PartialEq, Clone)]
pub struct TextSpan {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) literal: String,
}

impl TextSpan {
    pub fn new(start: usize, end: usize, literal: String) -> Self {
        Self { start, end, literal }
    }

    pub fn length(&self) -> usize {
        self.end - self.start
    }

    pub fn combine(mut spans: Vec<TextSpan>) -> TextSpan {
        spans.sort_by(
            |a, b| a.start.cmp(&b.start)
        );

        let start = spans.first().unwrap().start;
        let end = spans.last().unwrap().end;

        let mut literal = String::new();
        for (index, span) in spans.iter().enumerate() {
            if index > 0 {
                let last = spans.get(index - 1).unwrap();
                // Prevent overflow by checking if spans are properly ordered
                let diff = if span.start >= last.end {
                    span.start - last.end
                } else {
                    0
                };

                literal.push_str(&" ".repeat(diff));
            }
            literal.push_str(&span.literal);
        }

        TextSpan::new(start, end, literal)
    }
}