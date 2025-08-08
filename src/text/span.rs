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

    pub fn default() -> Self {
        Self {
            start: 0,
            end: 0,
            literal: String::new(),
        }
    }

    pub fn length(&self) -> usize {
        self.end - self.start
    }

    pub fn combine(spans: Vec<TextSpan>) -> TextSpan {
        Self::combine_owned(spans)
    }

    /// Combine spans from references without intermediate cloning
    pub fn combine_refs(spans: &[&TextSpan]) -> TextSpan {
        if spans.is_empty() {
            return TextSpan::default();
        }
        
        let start = spans.iter().map(|s| s.start).min().unwrap();
        let end = spans.iter().map(|s| s.end).max().unwrap();
        
        // Sort spans by start position for proper literal reconstruction
        let mut sorted_spans = spans.to_vec();
        sorted_spans.sort_by(|a, b| a.start.cmp(&b.start));
        
        let mut literal = String::new();
        for (index, span) in sorted_spans.iter().enumerate() {
            if index > 0 {
                let last = sorted_spans[index - 1];
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

    /// Helper method to combine a vector of owned spans
    pub fn combine_owned(spans: Vec<TextSpan>) -> TextSpan {
        let span_refs: Vec<&TextSpan> = spans.iter().collect();
        Self::combine_refs(&span_refs)
    }

    /// Combine two spans without creating a vector
    pub fn combine_two(first: &TextSpan, second: &TextSpan) -> TextSpan {
        Self::combine_refs(&[first, second])
    }

    /// Combine three spans without creating a vector
    pub fn combine_three(first: &TextSpan, second: &TextSpan, third: &TextSpan) -> TextSpan {
        Self::combine_refs(&[first, second, third])
    }
}