// content-script.js - optional page extractor for DealPal (Amazon/Walmart/eBay-friendly)
(function() {
  function textOf(el) { return el ? (el.innerText || el.textContent || '').trim() : ''; }
  function visible(el) {
    if (!el) return false;
    const style = window.getComputedStyle(el);
    if (style && (style.visibility === 'hidden' || style.display === 'none')) return false;
    const rect = el.getBoundingClientRect();
    return rect && rect.width > 0 && rect.height > 0;
  }
  function numericFromText(s) {
    if (!s) return null;
    const m = s.match(/\$?\s*([0-9]{1,3}(?:[,\s][0-9]{3})*(?:\.[0-9]{2})?)/);
    if (!m) return null;
    return parseFloat(m[1].replace(/[,\s]/g, ''));
  }

  try {
    // Title heuristics
    const titleSelectors = ['#productTitle','h1.prod-ProductTitle','h1[itemprop="name"]','h1','[data-testid="product-title"]','.product-title','#itemTitle'];
    let title = '';
    for (const sel of titleSelectors) {
      const el = document.querySelector(sel);
      if (el && textOf(el).length) { title = textOf(el); break; }
    }
    if (!title) title = document.title || '';

    // price detection
    let priceText = null;
    const host = location.hostname || '';
    if (host.includes('amazon.')) {
      const amazonSelectors = ['#priceblock_ourprice','#priceblock_dealprice','#priceblock_saleprice','#price_inside_buybox','.a-price .a-offscreen'];
      for (const s of amazonSelectors) { const el=document.querySelector(s); if(el&&textOf(el)){priceText=textOf(el);break;} }
    }
    if (!priceText && host.includes('walmart.')) {
      const walmartSelectors = ['[itemprop="price"]','[data-testid="price"]','.price-characteristic','.prod-PriceHero .price-characteristic','.price .visuallyhidden'];
      for (const s of walmartSelectors) { const el=document.querySelector(s); if(el&&textOf(el)){priceText=textOf(el);break;} }
      if (!priceText) { const meta=document.querySelector('meta[property="og:price:amount"], meta[itemprop="price"]'); if(meta&&meta.content) priceText=meta.content; }
    }
    if (!priceText && host.includes('ebay.')) {
      const ebaySelectors = ['#prcIsum','#mm-saleDscPrc','.display-price','.notranslate','[itemprop="price"]','.vi-price'];
      for (const s of ebaySelectors) { const el=document.querySelector(s); if(el&&textOf(el)){priceText=textOf(el);break;} }
      if (!priceText) { const meta=document.querySelector('meta[itemprop="price"], meta[property="product:price:amount"]'); if(meta&&meta.content) priceText=meta.content; }
    }

    // fallback: scan visible elements for $... text
    if (!priceText) {
      const dollarRegex = /\$\s*\d/;
      const els = Array.from(document.querySelectorAll('span,div,li,button,a'));
      const visibleEls = els.filter(e => visible(e) && (textOf(e) && dollarRegex.test(textOf(e))));
      let candidate = visibleEls[0] || null;
      if (candidate) priceText = textOf(candidate);
    }

    const numeric = numericFromText(priceText);

    const productInfo = { title: title || '', priceText: priceText || null, price: numeric, url: location.href, ts: Date.now() };

    // send to runtime for listeners
    if (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.sendMessage) {
      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: productInfo });
    }
  } catch (err) {
    console.error('content-script extractor error', err);
    if (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.sendMessage) {
      chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload: { title: document.title || '', priceText: null, price: null, url: location.href, ts: Date.now() } });
    }
  }
})();
