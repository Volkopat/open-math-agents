/** A visible "Post on X" button with a prefilled post. Server component: a plain link to X's post intent. */
export function xIntent(text: string, url: string) {
  return `https://x.com/intent/post?text=${encodeURIComponent(text)}&url=${encodeURIComponent(url)}`;
}

const Logo = () => (
  <svg viewBox="0 0 24 24" width="16" height="16" aria-hidden="true" fill="currentColor">
    <path d="M18.244 2.25h3.308l-7.227 8.26 8.502 11.24H16.17l-5.214-6.817L4.99 21.75H1.68l7.73-8.835L1.254 2.25H8.08l4.713 6.231zm-1.161 17.52h1.833L7.084 4.126H5.117z" />
  </svg>
);

export default function ShareX({ text, url, label = "Post on X", small }: { text: string; url: string; label?: string; small?: boolean }) {
  return (
    <a className={small ? "xbtn small" : "xbtn"} href={xIntent(text, url)} target="_blank" rel="noreferrer">
      <Logo /> {label}
    </a>
  );
}

/** A card that invites people to post a result, with the text they will post shown before they click. */
export function ShareXCard({ title, text, url, label }: { title: string; text: string; url: string; label?: string }) {
  return (
    <section className="xcard">
      <div className="xcard-body">
        <div className="xcard-title">{title}</div>
        <p className="xcard-preview">“{text}” <span>{url.replace(/^https?:\/\//, "")}</span></p>
      </div>
      <ShareX text={text} url={url} label={label} />
    </section>
  );
}
